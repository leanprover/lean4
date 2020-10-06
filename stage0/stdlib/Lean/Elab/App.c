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
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_28__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
extern lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___closed__3;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__toMessageList(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__12;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__23;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__13;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__11;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__7;
extern lean_object* l_Lean_fieldIdxKind___closed__2;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__elabAppAux___closed__1;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__11;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
lean_object* l___private_Lean_Elab_App_28__elabAppAux___closed__2;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__mergeFailures(lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_4__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__3;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
extern lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__elabAppAux___closed__3;
lean_object* l___private_Lean_Elab_Util_2__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__17;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__8;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_8__nextArgIsHole___boxed(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__11;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___closed__2;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__27;
lean_object* l_Lean_Elab_Term_expandApp___closed__1;
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_3__tryCoeFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__7;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__4;
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__2;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_24__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__9;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__1;
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__6;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_21__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__14;
lean_object* l___private_Lean_Elab_App_22__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__6;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__5;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_7__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__1;
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__9;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__18;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__1;
lean_object* l___private_Lean_Elab_App_5__hasTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__8;
lean_object* l___private_Lean_Elab_App_11__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__7;
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__2;
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_3__tryCoeFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__10;
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__5;
lean_object* l___private_Lean_Elab_App_30__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_12__findMethod_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_App_11__throwLValError(lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__3;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2;
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__22;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_5__hasTypeMVar(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__8;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_4__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__8;
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__9;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__4;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__6;
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_importModules___closed__1;
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__1;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l___private_Lean_Elab_App_16__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_App_25__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_27__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__6;
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__5;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__14;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__4;
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___closed__3;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_16__useImplicitLambda_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Elab_setMacroStackOption(lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_App_25__toMessageData___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
uint8_t l___private_Lean_Elab_App_6__hasOnlyTypeMVar(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__getForallBody___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__16;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_27__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
lean_object* l___private_Lean_Elab_App_14__consumeImplicits___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__13;
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_App_26__toMessageList___boxed(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___closed__8;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__10;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__getSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__20;
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_8__exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___closed__2;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_6__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_8__nextArgIsHole(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__19;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__7;
lean_object* l___private_Lean_Elab_App_11__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__8;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_App_23__isSuccess___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__10;
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
uint8_t l___private_Lean_Elab_App_23__isSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_12__findMethod_x3f___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__3;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_7__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_14__consumeImplicits___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__10;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__3;
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__26;
lean_object* l___private_Lean_Elab_Term_19__elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__5;
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__7;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
extern lean_object* l___private_Lean_Elab_Term_12__isExplicit___closed__2;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
lean_object* l___private_Lean_Elab_App_12__findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__5;
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__consumeImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_App_20__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__4;
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___closed__3;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_12__findMethod_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_11 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_3__tryCoeFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_3__tryCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_3__tryCoeFun___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_3__tryCoeFun___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_3__tryCoeFun___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_3__tryCoeFun___closed__5;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_3__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_3__tryCoeFun___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
x_29 = l___private_Lean_Elab_App_3__tryCoeFun___closed__2;
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
x_71 = l___private_Lean_Elab_App_3__tryCoeFun___closed__8;
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
x_79 = l___private_Lean_Elab_App_3__tryCoeFun___closed__5;
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
x_45 = l___private_Lean_Elab_App_3__tryCoeFun___closed__5;
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
x_47 = l___private_Lean_Elab_App_3__tryCoeFun___closed__7;
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
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_3__tryCoeFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_3__tryCoeFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_3__tryCoeFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_3__tryCoeFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_4__getForallBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_App_4__getForallBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_4__getForallBody___main___spec__1(x_4, x_2, x_8);
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_4__getForallBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_4__getForallBody___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_4__getForallBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_4__getForallBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_5, x_4);
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
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_8, x_3);
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
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_16, x_3);
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
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_24, x_3);
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
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_32, x_3);
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
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_33, x_35);
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
uint8_t l___private_Lean_Elab_App_5__hasTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_2, x_3);
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
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_5__hasTypeMVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_5__hasTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_5__hasTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_5, x_4);
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
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_8, x_3);
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
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_16, x_3);
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
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_24, x_3);
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
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_32, x_3);
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
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_33, x_35);
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
uint8_t l___private_Lean_Elab_App_6__hasOnlyTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
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
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_6__hasOnlyTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_6__hasOnlyTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_7__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_29 = l___private_Lean_Elab_App_4__getForallBody___main(x_27, x_28, x_2);
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
x_34 = l___private_Lean_Elab_App_5__hasTypeMVar(x_1, x_32);
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
x_37 = l___private_Lean_Elab_App_6__hasOnlyTypeMVar(x_1, x_32);
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
x_40 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_18, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_66 = l___private_Lean_Elab_App_4__getForallBody___main(x_64, x_65, x_2);
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
x_71 = l___private_Lean_Elab_App_5__hasTypeMVar(x_1, x_69);
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
x_74 = l___private_Lean_Elab_App_6__hasOnlyTypeMVar(x_1, x_69);
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
x_77 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_18, x_69, x_3, x_4, x_5, x_6, x_60, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_7__propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
uint8_t l___private_Lean_Elab_App_8__nextArgIsHole(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_App_8__nextArgIsHole___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_8__nextArgIsHole(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_17 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_16, x_2, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_4 = x_20;
x_11 = x_18;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_17 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_16, x_2, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_4 = x_20;
x_11 = x_18;
goto _start;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1;
x_2 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16() {
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
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_60; 
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
x_60 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_16__useImplicitLambda_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 7)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_61, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_61, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_61, 2);
lean_inc(x_120);
x_121 = lean_ctor_get_uint64(x_61, sizeof(void*)*3);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3(x_118, x_16, x_122);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; lean_object* x_125; 
x_124 = (uint8_t)((x_121 << 24) >> 61);
x_125 = lean_box(x_124);
switch (lean_obj_tag(x_125)) {
case 1:
{
if (x_14 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_142; 
lean_dec(x_118);
lean_dec(x_61);
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
 x_126 = x_1;
} else {
 lean_dec_ref(x_1);
 x_126 = lean_box(0);
}
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_119);
x_128 = 0;
x_129 = lean_box(0);
lean_inc(x_6);
x_130 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_127, x_128, x_129, x_6, x_7, x_8, x_9, x_62);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_131);
x_142 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5(x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_132);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_133 = x_18;
x_134 = x_145;
goto block_141;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = l_Lean_Expr_mvarId_x21(x_131);
x_148 = lean_array_push(x_18, x_147);
x_133 = x_148;
x_134 = x_146;
goto block_141;
}
}
else
{
uint8_t x_149; 
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_120);
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
x_149 = !lean_is_exclusive(x_142);
if (x_149 == 0)
{
return x_142;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_142, 0);
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_142);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
block_141:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = l_Lean_Expr_mvarId_x21(x_131);
x_136 = lean_array_push(x_19, x_135);
if (lean_is_scalar(x_126)) {
 x_137 = lean_alloc_ctor(0, 8, 2);
} else {
 x_137 = x_126;
}
lean_ctor_set(x_137, 0, x_11);
lean_ctor_set(x_137, 1, x_12);
lean_ctor_set(x_137, 2, x_13);
lean_ctor_set(x_137, 3, x_15);
lean_ctor_set(x_137, 4, x_16);
lean_ctor_set(x_137, 5, x_17);
lean_ctor_set(x_137, 6, x_133);
lean_ctor_set(x_137, 7, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_137, sizeof(void*)*8 + 1, x_21);
lean_inc(x_131);
x_138 = l_Lean_mkApp(x_2, x_131);
x_139 = lean_expr_instantiate1(x_120, x_131);
lean_dec(x_131);
lean_dec(x_120);
x_1 = x_137;
x_2 = x_138;
x_3 = x_139;
x_10 = x_134;
goto _start;
}
}
else
{
lean_object* x_153; uint8_t x_154; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_153 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
x_154 = !lean_is_exclusive(x_1);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_1, 7);
lean_dec(x_155);
x_156 = lean_ctor_get(x_1, 6);
lean_dec(x_156);
x_157 = lean_ctor_get(x_1, 5);
lean_dec(x_157);
x_158 = lean_ctor_get(x_1, 4);
lean_dec(x_158);
x_159 = lean_ctor_get(x_1, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_1, 2);
lean_dec(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_1, 0);
lean_dec(x_162);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_153, 1);
lean_inc(x_163);
lean_dec(x_153);
x_164 = lean_array_get_size(x_12);
x_165 = lean_nat_dec_lt(x_15, x_164);
lean_dec(x_164);
if (x_165 == 0)
{
uint8_t x_166; 
lean_free_object(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_166 = l_Array_isEmpty___rarg(x_16);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_167 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_167, 0, x_118);
x_168 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_169 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
x_170 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_171 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = x_16;
x_173 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_172);
x_174 = x_173;
x_175 = l_Array_toList___rarg(x_174);
lean_dec(x_174);
x_176 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_175);
x_177 = l_Array_HasRepr___rarg___closed__1;
x_178 = lean_string_append(x_177, x_176);
lean_dec(x_176);
x_179 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_181, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; 
lean_dec(x_118);
lean_dec(x_16);
x_183 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_184 = l_Lean_checkTraceOption(x_22, x_183);
lean_dec(x_22);
if (x_184 == 0)
{
x_27 = x_163;
goto block_59;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_inc(x_2);
x_185 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_185, 0, x_2);
x_186 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_183, x_185, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_27 = x_187;
goto block_59;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_188 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_189 = l___private_Lean_Elab_App_2__elabArg(x_2, x_188, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_unsigned_to_nat(1u);
x_193 = lean_nat_add(x_15, x_192);
lean_dec(x_15);
x_194 = 1;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_194);
lean_inc(x_190);
x_195 = l_Lean_mkApp(x_2, x_190);
x_196 = lean_expr_instantiate1(x_120, x_190);
lean_dec(x_190);
lean_dec(x_120);
x_2 = x_195;
x_3 = x_196;
x_10 = x_191;
goto _start;
}
else
{
uint8_t x_198; 
lean_free_object(x_1);
lean_dec(x_120);
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
x_198 = !lean_is_exclusive(x_189);
if (x_198 == 0)
{
return x_189;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_189, 0);
x_200 = lean_ctor_get(x_189, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_189);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
else
{
uint8_t x_202; 
lean_free_object(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
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
x_202 = !lean_is_exclusive(x_153);
if (x_202 == 0)
{
return x_153;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_153, 0);
x_204 = lean_ctor_get(x_153, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_153);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_153, 1);
lean_inc(x_206);
lean_dec(x_153);
x_207 = lean_array_get_size(x_12);
x_208 = lean_nat_dec_lt(x_15, x_207);
lean_dec(x_207);
if (x_208 == 0)
{
uint8_t x_209; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_209 = l_Array_isEmpty___rarg(x_16);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_210 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_210, 0, x_118);
x_211 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_212 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_214 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = x_16;
x_216 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_215);
x_217 = x_216;
x_218 = l_Array_toList___rarg(x_217);
lean_dec(x_217);
x_219 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_218);
x_220 = l_Array_HasRepr___rarg___closed__1;
x_221 = lean_string_append(x_220, x_219);
lean_dec(x_219);
x_222 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_224 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_224, 0, x_214);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_224, x_4, x_5, x_6, x_7, x_8, x_9, x_206);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_225;
}
else
{
lean_object* x_226; uint8_t x_227; 
lean_dec(x_118);
lean_dec(x_16);
x_226 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_227 = l_Lean_checkTraceOption(x_22, x_226);
lean_dec(x_22);
if (x_227 == 0)
{
x_27 = x_206;
goto block_59;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_inc(x_2);
x_228 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_228, 0, x_2);
x_229 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_226, x_228, x_4, x_5, x_6, x_7, x_8, x_9, x_206);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_27 = x_230;
goto block_59;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_231 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_232 = l___private_Lean_Elab_App_2__elabArg(x_2, x_231, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_206);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_add(x_15, x_235);
lean_dec(x_15);
x_237 = 1;
x_238 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_238, 0, x_11);
lean_ctor_set(x_238, 1, x_12);
lean_ctor_set(x_238, 2, x_13);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set(x_238, 4, x_16);
lean_ctor_set(x_238, 5, x_17);
lean_ctor_set(x_238, 6, x_18);
lean_ctor_set(x_238, 7, x_19);
lean_ctor_set_uint8(x_238, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_238, sizeof(void*)*8 + 1, x_237);
lean_inc(x_233);
x_239 = l_Lean_mkApp(x_2, x_233);
x_240 = lean_expr_instantiate1(x_120, x_233);
lean_dec(x_233);
lean_dec(x_120);
x_1 = x_238;
x_2 = x_239;
x_3 = x_240;
x_10 = x_234;
goto _start;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_120);
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
x_242 = lean_ctor_get(x_232, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_232, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_244 = x_232;
} else {
 lean_dec_ref(x_232);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
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
x_246 = lean_ctor_get(x_153, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_153, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_248 = x_153;
} else {
 lean_dec_ref(x_153);
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
}
}
case 3:
{
if (x_14 == 0)
{
uint8_t x_250; 
lean_dec(x_118);
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_3);
x_250 = !lean_is_exclusive(x_1);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_251 = lean_ctor_get(x_1, 7);
lean_dec(x_251);
x_252 = lean_ctor_get(x_1, 6);
lean_dec(x_252);
x_253 = lean_ctor_get(x_1, 5);
lean_dec(x_253);
x_254 = lean_ctor_get(x_1, 4);
lean_dec(x_254);
x_255 = lean_ctor_get(x_1, 3);
lean_dec(x_255);
x_256 = lean_ctor_get(x_1, 2);
lean_dec(x_256);
x_257 = lean_ctor_get(x_1, 1);
lean_dec(x_257);
x_258 = lean_ctor_get(x_1, 0);
lean_dec(x_258);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_119);
x_260 = 1;
x_261 = lean_box(0);
lean_inc(x_6);
x_262 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_259, x_260, x_261, x_6, x_7, x_8, x_9, x_62);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lean_Expr_mvarId_x21(x_263);
x_266 = lean_array_push(x_17, x_265);
lean_ctor_set(x_1, 5, x_266);
lean_inc(x_263);
x_267 = l_Lean_mkApp(x_2, x_263);
x_268 = lean_expr_instantiate1(x_120, x_263);
lean_dec(x_263);
lean_dec(x_120);
x_2 = x_267;
x_3 = x_268;
x_10 = x_264;
goto _start;
}
else
{
lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_1);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_119);
x_271 = 1;
x_272 = lean_box(0);
lean_inc(x_6);
x_273 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_270, x_271, x_272, x_6, x_7, x_8, x_9, x_62);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_Expr_mvarId_x21(x_274);
x_277 = lean_array_push(x_17, x_276);
x_278 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_278, 0, x_11);
lean_ctor_set(x_278, 1, x_12);
lean_ctor_set(x_278, 2, x_13);
lean_ctor_set(x_278, 3, x_15);
lean_ctor_set(x_278, 4, x_16);
lean_ctor_set(x_278, 5, x_277);
lean_ctor_set(x_278, 6, x_18);
lean_ctor_set(x_278, 7, x_19);
lean_ctor_set_uint8(x_278, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_278, sizeof(void*)*8 + 1, x_21);
lean_inc(x_274);
x_279 = l_Lean_mkApp(x_2, x_274);
x_280 = lean_expr_instantiate1(x_120, x_274);
lean_dec(x_274);
lean_dec(x_120);
x_1 = x_278;
x_2 = x_279;
x_3 = x_280;
x_10 = x_275;
goto _start;
}
}
else
{
uint8_t x_282; 
x_282 = l___private_Lean_Elab_App_8__nextArgIsHole(x_1);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_283 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
x_284 = !lean_is_exclusive(x_1);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = lean_ctor_get(x_1, 7);
lean_dec(x_285);
x_286 = lean_ctor_get(x_1, 6);
lean_dec(x_286);
x_287 = lean_ctor_get(x_1, 5);
lean_dec(x_287);
x_288 = lean_ctor_get(x_1, 4);
lean_dec(x_288);
x_289 = lean_ctor_get(x_1, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_1, 2);
lean_dec(x_290);
x_291 = lean_ctor_get(x_1, 1);
lean_dec(x_291);
x_292 = lean_ctor_get(x_1, 0);
lean_dec(x_292);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_283, 1);
lean_inc(x_293);
lean_dec(x_283);
x_294 = lean_array_get_size(x_12);
x_295 = lean_nat_dec_lt(x_15, x_294);
lean_dec(x_294);
if (x_295 == 0)
{
uint8_t x_296; 
lean_free_object(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_296 = l_Array_isEmpty___rarg(x_16);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_297 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_297, 0, x_118);
x_298 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_299 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_301 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = x_16;
x_303 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_302);
x_304 = x_303;
x_305 = l_Array_toList___rarg(x_304);
lean_dec(x_304);
x_306 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_305);
x_307 = l_Array_HasRepr___rarg___closed__1;
x_308 = lean_string_append(x_307, x_306);
lean_dec(x_306);
x_309 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_311, 0, x_301);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_311, x_4, x_5, x_6, x_7, x_8, x_9, x_293);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_312;
}
else
{
lean_object* x_313; uint8_t x_314; 
lean_dec(x_118);
lean_dec(x_16);
x_313 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_314 = l_Lean_checkTraceOption(x_22, x_313);
lean_dec(x_22);
if (x_314 == 0)
{
x_27 = x_293;
goto block_59;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_inc(x_2);
x_315 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_315, 0, x_2);
x_316 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_313, x_315, x_4, x_5, x_6, x_7, x_8, x_9, x_293);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_27 = x_317;
goto block_59;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_318 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_319 = l___private_Lean_Elab_App_2__elabArg(x_2, x_318, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_293);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_nat_add(x_15, x_322);
lean_dec(x_15);
x_324 = 1;
lean_ctor_set(x_1, 3, x_323);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_324);
lean_inc(x_320);
x_325 = l_Lean_mkApp(x_2, x_320);
x_326 = lean_expr_instantiate1(x_120, x_320);
lean_dec(x_320);
lean_dec(x_120);
x_2 = x_325;
x_3 = x_326;
x_10 = x_321;
goto _start;
}
else
{
uint8_t x_328; 
lean_free_object(x_1);
lean_dec(x_120);
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
x_328 = !lean_is_exclusive(x_319);
if (x_328 == 0)
{
return x_319;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_319, 0);
x_330 = lean_ctor_get(x_319, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_319);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
else
{
uint8_t x_332; 
lean_free_object(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
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
x_332 = !lean_is_exclusive(x_283);
if (x_332 == 0)
{
return x_283;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_283, 0);
x_334 = lean_ctor_get(x_283, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_283);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; 
x_336 = lean_ctor_get(x_283, 1);
lean_inc(x_336);
lean_dec(x_283);
x_337 = lean_array_get_size(x_12);
x_338 = lean_nat_dec_lt(x_15, x_337);
lean_dec(x_337);
if (x_338 == 0)
{
uint8_t x_339; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_339 = l_Array_isEmpty___rarg(x_16);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_340 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_340, 0, x_118);
x_341 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_342 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_344 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
x_345 = x_16;
x_346 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_345);
x_347 = x_346;
x_348 = l_Array_toList___rarg(x_347);
lean_dec(x_347);
x_349 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_348);
x_350 = l_Array_HasRepr___rarg___closed__1;
x_351 = lean_string_append(x_350, x_349);
lean_dec(x_349);
x_352 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_352, 0, x_351);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_352);
x_354 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_354, 0, x_344);
lean_ctor_set(x_354, 1, x_353);
x_355 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_354, x_4, x_5, x_6, x_7, x_8, x_9, x_336);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_355;
}
else
{
lean_object* x_356; uint8_t x_357; 
lean_dec(x_118);
lean_dec(x_16);
x_356 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_357 = l_Lean_checkTraceOption(x_22, x_356);
lean_dec(x_22);
if (x_357 == 0)
{
x_27 = x_336;
goto block_59;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_inc(x_2);
x_358 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_358, 0, x_2);
x_359 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_356, x_358, x_4, x_5, x_6, x_7, x_8, x_9, x_336);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_27 = x_360;
goto block_59;
}
}
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_361 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_362 = l___private_Lean_Elab_App_2__elabArg(x_2, x_361, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_336);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_unsigned_to_nat(1u);
x_366 = lean_nat_add(x_15, x_365);
lean_dec(x_15);
x_367 = 1;
x_368 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_368, 0, x_11);
lean_ctor_set(x_368, 1, x_12);
lean_ctor_set(x_368, 2, x_13);
lean_ctor_set(x_368, 3, x_366);
lean_ctor_set(x_368, 4, x_16);
lean_ctor_set(x_368, 5, x_17);
lean_ctor_set(x_368, 6, x_18);
lean_ctor_set(x_368, 7, x_19);
lean_ctor_set_uint8(x_368, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_368, sizeof(void*)*8 + 1, x_367);
lean_inc(x_363);
x_369 = l_Lean_mkApp(x_2, x_363);
x_370 = lean_expr_instantiate1(x_120, x_363);
lean_dec(x_363);
lean_dec(x_120);
x_1 = x_368;
x_2 = x_369;
x_3 = x_370;
x_10 = x_364;
goto _start;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_120);
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
x_372 = lean_ctor_get(x_362, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_362, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_374 = x_362;
} else {
 lean_dec_ref(x_362);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
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
x_376 = lean_ctor_get(x_283, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_283, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_378 = x_283;
} else {
 lean_dec_ref(x_283);
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
}
else
{
uint8_t x_380; 
lean_dec(x_118);
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_3);
x_380 = !lean_is_exclusive(x_1);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_381 = lean_ctor_get(x_1, 7);
lean_dec(x_381);
x_382 = lean_ctor_get(x_1, 6);
lean_dec(x_382);
x_383 = lean_ctor_get(x_1, 5);
lean_dec(x_383);
x_384 = lean_ctor_get(x_1, 4);
lean_dec(x_384);
x_385 = lean_ctor_get(x_1, 3);
lean_dec(x_385);
x_386 = lean_ctor_get(x_1, 2);
lean_dec(x_386);
x_387 = lean_ctor_get(x_1, 1);
lean_dec(x_387);
x_388 = lean_ctor_get(x_1, 0);
lean_dec(x_388);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_119);
x_390 = 1;
x_391 = lean_box(0);
lean_inc(x_6);
x_392 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_389, x_390, x_391, x_6, x_7, x_8, x_9, x_62);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_unsigned_to_nat(1u);
x_396 = lean_nat_add(x_15, x_395);
lean_dec(x_15);
x_397 = l_Lean_Expr_mvarId_x21(x_393);
x_398 = lean_array_push(x_17, x_397);
lean_ctor_set(x_1, 5, x_398);
lean_ctor_set(x_1, 3, x_396);
lean_inc(x_393);
x_399 = l_Lean_mkApp(x_2, x_393);
x_400 = lean_expr_instantiate1(x_120, x_393);
lean_dec(x_393);
lean_dec(x_120);
x_2 = x_399;
x_3 = x_400;
x_10 = x_394;
goto _start;
}
else
{
lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_1);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_119);
x_403 = 1;
x_404 = lean_box(0);
lean_inc(x_6);
x_405 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_402, x_403, x_404, x_6, x_7, x_8, x_9, x_62);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_unsigned_to_nat(1u);
x_409 = lean_nat_add(x_15, x_408);
lean_dec(x_15);
x_410 = l_Lean_Expr_mvarId_x21(x_406);
x_411 = lean_array_push(x_17, x_410);
x_412 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_412, 0, x_11);
lean_ctor_set(x_412, 1, x_12);
lean_ctor_set(x_412, 2, x_13);
lean_ctor_set(x_412, 3, x_409);
lean_ctor_set(x_412, 4, x_16);
lean_ctor_set(x_412, 5, x_411);
lean_ctor_set(x_412, 6, x_18);
lean_ctor_set(x_412, 7, x_19);
lean_ctor_set_uint8(x_412, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_412, sizeof(void*)*8 + 1, x_21);
lean_inc(x_406);
x_413 = l_Lean_mkApp(x_2, x_406);
x_414 = lean_expr_instantiate1(x_120, x_406);
lean_dec(x_406);
lean_dec(x_120);
x_1 = x_412;
x_2 = x_413;
x_3 = x_414;
x_10 = x_407;
goto _start;
}
}
}
}
default: 
{
lean_object* x_416; uint8_t x_417; 
lean_dec(x_125);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_416 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
x_417 = !lean_is_exclusive(x_1);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_418 = lean_ctor_get(x_1, 7);
lean_dec(x_418);
x_419 = lean_ctor_get(x_1, 6);
lean_dec(x_419);
x_420 = lean_ctor_get(x_1, 5);
lean_dec(x_420);
x_421 = lean_ctor_get(x_1, 4);
lean_dec(x_421);
x_422 = lean_ctor_get(x_1, 3);
lean_dec(x_422);
x_423 = lean_ctor_get(x_1, 2);
lean_dec(x_423);
x_424 = lean_ctor_get(x_1, 1);
lean_dec(x_424);
x_425 = lean_ctor_get(x_1, 0);
lean_dec(x_425);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; 
x_426 = lean_ctor_get(x_416, 1);
lean_inc(x_426);
lean_dec(x_416);
x_427 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_427);
x_428 = lean_array_get_size(x_12);
x_429 = lean_nat_dec_lt(x_15, x_428);
lean_dec(x_428);
if (x_429 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_430; 
x_430 = l_Lean_Expr_getOptParamDefault_x3f(x_119);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = l_Lean_Expr_getAutoParamTactic_x3f(x_119);
if (lean_obj_tag(x_431) == 0)
{
uint8_t x_432; 
lean_dec(x_1);
lean_dec(x_120);
lean_dec(x_119);
x_432 = l_Array_isEmpty___rarg(x_16);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_433 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_433, 0, x_118);
x_434 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_435 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_433);
x_436 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_437 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = x_16;
x_439 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_438);
x_440 = x_439;
x_441 = l_Array_toList___rarg(x_440);
lean_dec(x_440);
x_442 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_441);
x_443 = l_Array_HasRepr___rarg___closed__1;
x_444 = lean_string_append(x_443, x_442);
lean_dec(x_442);
x_445 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_447 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_447, 0, x_437);
lean_ctor_set(x_447, 1, x_446);
x_448 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_447, x_4, x_5, x_6, x_7, x_8, x_9, x_426);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_448;
}
else
{
lean_object* x_449; uint8_t x_450; 
lean_dec(x_118);
lean_dec(x_16);
x_449 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_450 = l_Lean_checkTraceOption(x_22, x_449);
lean_dec(x_22);
if (x_450 == 0)
{
x_27 = x_426;
goto block_59;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_inc(x_2);
x_451 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_451, 0, x_2);
x_452 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_449, x_451, x_4, x_5, x_6, x_7, x_8, x_9, x_426);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
x_27 = x_453;
goto block_59;
}
}
}
else
{
lean_object* x_454; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_454 = lean_ctor_get(x_431, 0);
lean_inc(x_454);
lean_dec(x_431);
if (lean_obj_tag(x_454) == 4)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
lean_dec(x_454);
x_456 = lean_st_ref_get(x_9, x_426);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
lean_dec(x_457);
x_460 = l___private_Lean_Elab_Util_2__evalSyntaxConstantUnsafe(x_459, x_455);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_11);
lean_dec(x_2);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_463 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_463, x_4, x_5, x_6, x_7, x_8, x_9, x_458);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_465 = lean_ctor_get(x_460, 0);
lean_inc(x_465);
lean_dec(x_460);
x_466 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_458);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_468 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_467);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_470 = l_Lean_Syntax_getArgs(x_465);
lean_dec(x_465);
x_471 = l_Array_empty___closed__1;
x_472 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_470, x_470, x_122, x_471);
lean_dec(x_470);
x_473 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_474 = lean_array_push(x_472, x_473);
x_475 = l_Lean_nullKind___closed__2;
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_474);
x_477 = lean_array_push(x_471, x_476);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_477);
x_479 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_480 = lean_array_push(x_479, x_478);
x_481 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16;
x_482 = lean_array_push(x_480, x_481);
x_483 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = lean_array_push(x_471, x_484);
x_486 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15;
x_489 = lean_array_push(x_488, x_487);
x_490 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_489);
x_492 = l_Lean_Syntax_copyInfo(x_491, x_11);
lean_dec(x_11);
x_493 = l_Lean_Expr_getAppNumArgsAux___main(x_119, x_122);
x_494 = lean_nat_sub(x_493, x_122);
lean_dec(x_493);
x_495 = lean_unsigned_to_nat(1u);
x_496 = lean_nat_sub(x_494, x_495);
lean_dec(x_494);
x_497 = l_Lean_Expr_getRevArg_x21___main(x_119, x_496);
lean_dec(x_119);
x_498 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_498, 0, x_492);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_499 = l___private_Lean_Elab_App_2__elabArg(x_2, x_498, x_497, x_4, x_5, x_6, x_7, x_8, x_9, x_469);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
lean_inc(x_500);
x_502 = l_Lean_mkApp(x_2, x_500);
x_503 = lean_expr_instantiate1(x_120, x_500);
lean_dec(x_500);
lean_dec(x_120);
x_2 = x_502;
x_3 = x_503;
x_10 = x_501;
goto _start;
}
else
{
uint8_t x_505; 
lean_dec(x_1);
lean_dec(x_120);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_505 = !lean_is_exclusive(x_499);
if (x_505 == 0)
{
return x_499;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_499, 0);
x_507 = lean_ctor_get(x_499, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_499);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
}
else
{
lean_object* x_509; lean_object* x_510; 
lean_dec(x_454);
lean_dec(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_11);
lean_dec(x_2);
x_509 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12;
x_510 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_509, x_4, x_5, x_6, x_7, x_8, x_9, x_426);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_510;
}
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_511 = lean_ctor_get(x_430, 0);
lean_inc(x_511);
lean_dec(x_430);
lean_inc(x_511);
x_512 = l_Lean_mkApp(x_2, x_511);
x_513 = lean_expr_instantiate1(x_120, x_511);
lean_dec(x_511);
lean_dec(x_120);
x_2 = x_512;
x_3 = x_513;
x_10 = x_426;
goto _start;
}
}
else
{
uint8_t x_515; 
lean_dec(x_1);
lean_dec(x_120);
lean_dec(x_119);
x_515 = l_Array_isEmpty___rarg(x_16);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_516 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_516, 0, x_118);
x_517 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_518 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_516);
x_519 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_520 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
x_521 = x_16;
x_522 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_521);
x_523 = x_522;
x_524 = l_Array_toList___rarg(x_523);
lean_dec(x_523);
x_525 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_524);
x_526 = l_Array_HasRepr___rarg___closed__1;
x_527 = lean_string_append(x_526, x_525);
lean_dec(x_525);
x_528 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_528, 0, x_527);
x_529 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_529, 0, x_528);
x_530 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_530, 0, x_520);
lean_ctor_set(x_530, 1, x_529);
x_531 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_530, x_4, x_5, x_6, x_7, x_8, x_9, x_426);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_531;
}
else
{
lean_object* x_532; uint8_t x_533; 
lean_dec(x_118);
lean_dec(x_16);
x_532 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_533 = l_Lean_checkTraceOption(x_22, x_532);
lean_dec(x_22);
if (x_533 == 0)
{
x_27 = x_426;
goto block_59;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_inc(x_2);
x_534 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_534, 0, x_2);
x_535 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_532, x_534, x_4, x_5, x_6, x_7, x_8, x_9, x_426);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_27 = x_536;
goto block_59;
}
}
}
}
else
{
lean_object* x_537; lean_object* x_538; 
lean_dec(x_1);
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_537 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_538 = l___private_Lean_Elab_App_2__elabArg(x_2, x_537, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_426);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_unsigned_to_nat(1u);
x_542 = lean_nat_add(x_15, x_541);
lean_dec(x_15);
x_543 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_543, 0, x_11);
lean_ctor_set(x_543, 1, x_12);
lean_ctor_set(x_543, 2, x_13);
lean_ctor_set(x_543, 3, x_542);
lean_ctor_set(x_543, 4, x_16);
lean_ctor_set(x_543, 5, x_17);
lean_ctor_set(x_543, 6, x_18);
lean_ctor_set(x_543, 7, x_19);
lean_ctor_set_uint8(x_543, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_543, sizeof(void*)*8 + 1, x_427);
lean_inc(x_539);
x_544 = l_Lean_mkApp(x_2, x_539);
x_545 = lean_expr_instantiate1(x_120, x_539);
lean_dec(x_539);
lean_dec(x_120);
x_1 = x_543;
x_2 = x_544;
x_3 = x_545;
x_10 = x_540;
goto _start;
}
else
{
uint8_t x_547; 
lean_dec(x_120);
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
x_547 = !lean_is_exclusive(x_538);
if (x_547 == 0)
{
return x_538;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_538, 0);
x_549 = lean_ctor_get(x_538, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_538);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
}
else
{
uint8_t x_551; 
lean_free_object(x_1);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
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
x_551 = !lean_is_exclusive(x_416);
if (x_551 == 0)
{
return x_416;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_416, 0);
x_553 = lean_ctor_get(x_416, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_416);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_555; uint8_t x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_555 = lean_ctor_get(x_416, 1);
lean_inc(x_555);
lean_dec(x_416);
x_556 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_557 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_557, 0, x_11);
lean_ctor_set(x_557, 1, x_12);
lean_ctor_set(x_557, 2, x_13);
lean_ctor_set(x_557, 3, x_15);
lean_ctor_set(x_557, 4, x_16);
lean_ctor_set(x_557, 5, x_17);
lean_ctor_set(x_557, 6, x_18);
lean_ctor_set(x_557, 7, x_19);
lean_ctor_set_uint8(x_557, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_557, sizeof(void*)*8 + 1, x_556);
x_558 = lean_array_get_size(x_12);
x_559 = lean_nat_dec_lt(x_15, x_558);
lean_dec(x_558);
if (x_559 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_560; 
x_560 = l_Lean_Expr_getOptParamDefault_x3f(x_119);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; 
x_561 = l_Lean_Expr_getAutoParamTactic_x3f(x_119);
if (lean_obj_tag(x_561) == 0)
{
uint8_t x_562; 
lean_dec(x_557);
lean_dec(x_120);
lean_dec(x_119);
x_562 = l_Array_isEmpty___rarg(x_16);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_563 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_563, 0, x_118);
x_564 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_565 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_563);
x_566 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_567 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
x_568 = x_16;
x_569 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_568);
x_570 = x_569;
x_571 = l_Array_toList___rarg(x_570);
lean_dec(x_570);
x_572 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_571);
x_573 = l_Array_HasRepr___rarg___closed__1;
x_574 = lean_string_append(x_573, x_572);
lean_dec(x_572);
x_575 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_575, 0, x_574);
x_576 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_576, 0, x_575);
x_577 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_577, 0, x_567);
lean_ctor_set(x_577, 1, x_576);
x_578 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_577, x_4, x_5, x_6, x_7, x_8, x_9, x_555);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_578;
}
else
{
lean_object* x_579; uint8_t x_580; 
lean_dec(x_118);
lean_dec(x_16);
x_579 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_580 = l_Lean_checkTraceOption(x_22, x_579);
lean_dec(x_22);
if (x_580 == 0)
{
x_27 = x_555;
goto block_59;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_inc(x_2);
x_581 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_581, 0, x_2);
x_582 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_579, x_581, x_4, x_5, x_6, x_7, x_8, x_9, x_555);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec(x_582);
x_27 = x_583;
goto block_59;
}
}
}
else
{
lean_object* x_584; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_584 = lean_ctor_get(x_561, 0);
lean_inc(x_584);
lean_dec(x_561);
if (lean_obj_tag(x_584) == 4)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
lean_dec(x_584);
x_586 = lean_st_ref_get(x_9, x_555);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_ctor_get(x_587, 0);
lean_inc(x_589);
lean_dec(x_587);
x_590 = l___private_Lean_Elab_Util_2__evalSyntaxConstantUnsafe(x_589, x_585);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_557);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_11);
lean_dec(x_2);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec(x_590);
x_592 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_592, 0, x_591);
x_593 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_593, 0, x_592);
x_594 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_593, x_4, x_5, x_6, x_7, x_8, x_9, x_588);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_594;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_595 = lean_ctor_get(x_590, 0);
lean_inc(x_595);
lean_dec(x_590);
x_596 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_588);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_598 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_597);
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
lean_dec(x_598);
x_600 = l_Lean_Syntax_getArgs(x_595);
lean_dec(x_595);
x_601 = l_Array_empty___closed__1;
x_602 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_600, x_600, x_122, x_601);
lean_dec(x_600);
x_603 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_604 = lean_array_push(x_602, x_603);
x_605 = l_Lean_nullKind___closed__2;
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_604);
x_607 = lean_array_push(x_601, x_606);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_607);
x_609 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_610 = lean_array_push(x_609, x_608);
x_611 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16;
x_612 = lean_array_push(x_610, x_611);
x_613 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_612);
x_615 = lean_array_push(x_601, x_614);
x_616 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_615);
x_618 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15;
x_619 = lean_array_push(x_618, x_617);
x_620 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_619);
x_622 = l_Lean_Syntax_copyInfo(x_621, x_11);
lean_dec(x_11);
x_623 = l_Lean_Expr_getAppNumArgsAux___main(x_119, x_122);
x_624 = lean_nat_sub(x_623, x_122);
lean_dec(x_623);
x_625 = lean_unsigned_to_nat(1u);
x_626 = lean_nat_sub(x_624, x_625);
lean_dec(x_624);
x_627 = l_Lean_Expr_getRevArg_x21___main(x_119, x_626);
lean_dec(x_119);
x_628 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_628, 0, x_622);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_629 = l___private_Lean_Elab_App_2__elabArg(x_2, x_628, x_627, x_4, x_5, x_6, x_7, x_8, x_9, x_599);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
lean_inc(x_630);
x_632 = l_Lean_mkApp(x_2, x_630);
x_633 = lean_expr_instantiate1(x_120, x_630);
lean_dec(x_630);
lean_dec(x_120);
x_1 = x_557;
x_2 = x_632;
x_3 = x_633;
x_10 = x_631;
goto _start;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_557);
lean_dec(x_120);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_635 = lean_ctor_get(x_629, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_629, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_637 = x_629;
} else {
 lean_dec_ref(x_629);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
}
else
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_584);
lean_dec(x_557);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_11);
lean_dec(x_2);
x_639 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12;
x_640 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_639, x_4, x_5, x_6, x_7, x_8, x_9, x_555);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_640;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_641 = lean_ctor_get(x_560, 0);
lean_inc(x_641);
lean_dec(x_560);
lean_inc(x_641);
x_642 = l_Lean_mkApp(x_2, x_641);
x_643 = lean_expr_instantiate1(x_120, x_641);
lean_dec(x_641);
lean_dec(x_120);
x_1 = x_557;
x_2 = x_642;
x_3 = x_643;
x_10 = x_555;
goto _start;
}
}
else
{
uint8_t x_645; 
lean_dec(x_557);
lean_dec(x_120);
lean_dec(x_119);
x_645 = l_Array_isEmpty___rarg(x_16);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_646 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_646, 0, x_118);
x_647 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_648 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_646);
x_649 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_650 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
x_651 = x_16;
x_652 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_122, x_651);
x_653 = x_652;
x_654 = l_Array_toList___rarg(x_653);
lean_dec(x_653);
x_655 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_654);
x_656 = l_Array_HasRepr___rarg___closed__1;
x_657 = lean_string_append(x_656, x_655);
lean_dec(x_655);
x_658 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_658, 0, x_657);
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
x_660 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_660, 0, x_650);
lean_ctor_set(x_660, 1, x_659);
x_661 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_660, x_4, x_5, x_6, x_7, x_8, x_9, x_555);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_661;
}
else
{
lean_object* x_662; uint8_t x_663; 
lean_dec(x_118);
lean_dec(x_16);
x_662 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_663 = l_Lean_checkTraceOption(x_22, x_662);
lean_dec(x_22);
if (x_663 == 0)
{
x_27 = x_555;
goto block_59;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_inc(x_2);
x_664 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_664, 0, x_2);
x_665 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_662, x_664, x_4, x_5, x_6, x_7, x_8, x_9, x_555);
x_666 = lean_ctor_get(x_665, 1);
lean_inc(x_666);
lean_dec(x_665);
x_27 = x_666;
goto block_59;
}
}
}
}
else
{
lean_object* x_667; lean_object* x_668; 
lean_dec(x_557);
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_667 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_668 = l___private_Lean_Elab_App_2__elabArg(x_2, x_667, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_555);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
x_671 = lean_unsigned_to_nat(1u);
x_672 = lean_nat_add(x_15, x_671);
lean_dec(x_15);
x_673 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_673, 0, x_11);
lean_ctor_set(x_673, 1, x_12);
lean_ctor_set(x_673, 2, x_13);
lean_ctor_set(x_673, 3, x_672);
lean_ctor_set(x_673, 4, x_16);
lean_ctor_set(x_673, 5, x_17);
lean_ctor_set(x_673, 6, x_18);
lean_ctor_set(x_673, 7, x_19);
lean_ctor_set_uint8(x_673, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_673, sizeof(void*)*8 + 1, x_556);
lean_inc(x_669);
x_674 = l_Lean_mkApp(x_2, x_669);
x_675 = lean_expr_instantiate1(x_120, x_669);
lean_dec(x_669);
lean_dec(x_120);
x_1 = x_673;
x_2 = x_674;
x_3 = x_675;
x_10 = x_670;
goto _start;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_120);
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
x_677 = lean_ctor_get(x_668, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_668, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_679 = x_668;
} else {
 lean_dec_ref(x_668);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
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
x_681 = lean_ctor_get(x_416, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_416, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_683 = x_416;
} else {
 lean_dec_ref(x_416);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_681);
lean_ctor_set(x_684, 1, x_682);
return x_684;
}
}
}
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_118);
lean_dec(x_22);
lean_dec(x_3);
x_685 = lean_ctor_get(x_123, 0);
lean_inc(x_685);
lean_dec(x_123);
x_686 = l_Lean_Elab_Term_NamedArg_inhabited;
x_687 = lean_array_get(x_686, x_16, x_685);
x_688 = l_Array_eraseIdx___rarg(x_16, x_685);
lean_dec(x_685);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_690 = l___private_Lean_Elab_App_2__elabArg(x_2, x_689, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_693 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_692);
x_694 = !lean_is_exclusive(x_1);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_695 = lean_ctor_get(x_1, 7);
lean_dec(x_695);
x_696 = lean_ctor_get(x_1, 6);
lean_dec(x_696);
x_697 = lean_ctor_get(x_1, 5);
lean_dec(x_697);
x_698 = lean_ctor_get(x_1, 4);
lean_dec(x_698);
x_699 = lean_ctor_get(x_1, 3);
lean_dec(x_699);
x_700 = lean_ctor_get(x_1, 2);
lean_dec(x_700);
x_701 = lean_ctor_get(x_1, 1);
lean_dec(x_701);
x_702 = lean_ctor_get(x_1, 0);
lean_dec(x_702);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_703; uint8_t x_704; lean_object* x_705; lean_object* x_706; 
x_703 = lean_ctor_get(x_693, 1);
lean_inc(x_703);
lean_dec(x_693);
x_704 = 1;
lean_ctor_set(x_1, 4, x_688);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_704);
lean_inc(x_691);
x_705 = l_Lean_mkApp(x_2, x_691);
x_706 = lean_expr_instantiate1(x_120, x_691);
lean_dec(x_691);
lean_dec(x_120);
x_2 = x_705;
x_3 = x_706;
x_10 = x_703;
goto _start;
}
else
{
uint8_t x_708; 
lean_free_object(x_1);
lean_dec(x_691);
lean_dec(x_688);
lean_dec(x_120);
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
x_708 = !lean_is_exclusive(x_693);
if (x_708 == 0)
{
return x_693;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_693, 0);
x_710 = lean_ctor_get(x_693, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_693);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_712 = lean_ctor_get(x_693, 1);
lean_inc(x_712);
lean_dec(x_693);
x_713 = 1;
x_714 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_714, 0, x_11);
lean_ctor_set(x_714, 1, x_12);
lean_ctor_set(x_714, 2, x_13);
lean_ctor_set(x_714, 3, x_15);
lean_ctor_set(x_714, 4, x_688);
lean_ctor_set(x_714, 5, x_17);
lean_ctor_set(x_714, 6, x_18);
lean_ctor_set(x_714, 7, x_19);
lean_ctor_set_uint8(x_714, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_714, sizeof(void*)*8 + 1, x_713);
lean_inc(x_691);
x_715 = l_Lean_mkApp(x_2, x_691);
x_716 = lean_expr_instantiate1(x_120, x_691);
lean_dec(x_691);
lean_dec(x_120);
x_1 = x_714;
x_2 = x_715;
x_3 = x_716;
x_10 = x_712;
goto _start;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_691);
lean_dec(x_688);
lean_dec(x_120);
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
x_718 = lean_ctor_get(x_693, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_693, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_720 = x_693;
} else {
 lean_dec_ref(x_693);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
}
else
{
uint8_t x_722; 
lean_dec(x_688);
lean_dec(x_120);
lean_dec(x_61);
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
x_722 = !lean_is_exclusive(x_690);
if (x_722 == 0)
{
return x_690;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_690, 0);
x_724 = lean_ctor_get(x_690, 1);
lean_inc(x_724);
lean_inc(x_723);
lean_dec(x_690);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_723);
lean_ctor_set(x_725, 1, x_724);
return x_725;
}
}
}
}
else
{
lean_object* x_726; 
lean_dec(x_1);
x_726 = lean_box(0);
x_63 = x_726;
goto block_117;
}
block_117:
{
lean_object* x_64; uint8_t x_107; 
lean_dec(x_63);
x_107 = l_Array_isEmpty___rarg(x_16);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_22);
lean_dec(x_3);
x_108 = lean_box(0);
x_64 = x_108;
goto block_106;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_array_get_size(x_12);
x_110 = lean_nat_dec_eq(x_15, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_22);
lean_dec(x_3);
x_111 = lean_box(0);
x_64 = x_111;
goto block_106;
}
else
{
lean_object* x_112; uint8_t x_113; 
lean_dec(x_61);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_112 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_113 = l_Lean_checkTraceOption(x_22, x_112);
lean_dec(x_22);
if (x_113 == 0)
{
x_27 = x_62;
goto block_59;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_inc(x_2);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_2);
x_115 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_112, x_114, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_27 = x_116;
goto block_59;
}
}
}
block_106:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_64);
x_65 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_66 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_17);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = 1;
x_69 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_68, x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Array_empty___closed__1;
x_73 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_73, 0, x_11);
lean_ctor_set(x_73, 1, x_12);
lean_ctor_set(x_73, 2, x_13);
lean_ctor_set(x_73, 3, x_15);
lean_ctor_set(x_73, 4, x_16);
lean_ctor_set(x_73, 5, x_72);
lean_ctor_set(x_73, 6, x_18);
lean_ctor_set(x_73, 7, x_19);
lean_ctor_set_uint8(x_73, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_73, sizeof(void*)*8 + 1, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_74 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_16__useImplicitLambda_x3f___spec__1(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 7)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_1 = x_73;
x_3 = x_75;
x_10 = x_76;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_79 = l___private_Lean_Elab_App_3__tryCoeFun(x_75, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_80);
x_82 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_1 = x_73;
x_2 = x_80;
x_3 = x_83;
x_10 = x_84;
goto _start;
}
else
{
uint8_t x_86; 
lean_dec(x_80);
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
uint8_t x_90; 
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
return x_79;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_79, 0);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_79);
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
uint8_t x_94; 
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_74);
if (x_94 == 0)
{
return x_74;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_74, 0);
x_96 = lean_ctor_get(x_74, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_74);
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
lean_dec(x_61);
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
x_98 = !lean_is_exclusive(x_70);
if (x_98 == 0)
{
return x_70;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_70, 0);
x_100 = lean_ctor_get(x_70, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_70);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_61);
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
x_102 = !lean_is_exclusive(x_66);
if (x_102 == 0)
{
return x_66;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_66, 0);
x_104 = lean_ctor_get(x_66, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_66);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
uint8_t x_727; 
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
x_727 = !lean_is_exclusive(x_60);
if (x_727 == 0)
{
return x_60;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_60, 0);
x_729 = lean_ctor_get(x_60, 1);
lean_inc(x_729);
lean_inc(x_728);
lean_dec(x_60);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_728);
lean_ctor_set(x_730, 1, x_729);
return x_730;
}
}
block_59:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_29 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_2);
x_31 = l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1(x_2, x_11, x_19, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_44 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_17);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_2);
x_46 = l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2(x_2, x_11, x_19, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_2);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
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
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
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
uint8_t x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_771; 
x_731 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_732 = lean_ctor_get(x_8, 0);
x_733 = lean_ctor_get(x_8, 1);
x_734 = lean_ctor_get(x_8, 2);
x_735 = lean_ctor_get(x_8, 3);
lean_inc(x_735);
lean_inc(x_734);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_8);
x_736 = l_Lean_replaceRef(x_11, x_735);
x_737 = l_Lean_replaceRef(x_736, x_735);
lean_dec(x_736);
x_738 = l_Lean_replaceRef(x_737, x_735);
lean_dec(x_735);
lean_dec(x_737);
lean_inc(x_732);
x_739 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_739, 0, x_732);
lean_ctor_set(x_739, 1, x_733);
lean_ctor_set(x_739, 2, x_734);
lean_ctor_set(x_739, 3, x_738);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_771 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_16__useImplicitLambda_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_739, x_9, x_10);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
if (lean_obj_tag(x_772) == 7)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; uint64_t x_832; lean_object* x_833; lean_object* x_834; 
x_829 = lean_ctor_get(x_772, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_772, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_772, 2);
lean_inc(x_831);
x_832 = lean_ctor_get_uint64(x_772, sizeof(void*)*3);
x_833 = lean_unsigned_to_nat(0u);
x_834 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3(x_829, x_16, x_833);
if (lean_obj_tag(x_834) == 0)
{
uint8_t x_835; lean_object* x_836; 
x_835 = (uint8_t)((x_832 << 24) >> 61);
x_836 = lean_box(x_835);
switch (lean_obj_tag(x_836)) {
case 1:
{
if (x_14 == 0)
{
lean_object* x_837; lean_object* x_838; uint8_t x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_853; 
lean_dec(x_829);
lean_dec(x_772);
lean_dec(x_732);
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
 x_837 = x_1;
} else {
 lean_dec_ref(x_1);
 x_837 = lean_box(0);
}
x_838 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_838, 0, x_830);
x_839 = 0;
x_840 = lean_box(0);
lean_inc(x_6);
x_841 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_838, x_839, x_840, x_6, x_7, x_739, x_9, x_773);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_842);
x_853 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5(x_842, x_4, x_5, x_6, x_7, x_739, x_9, x_843);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; uint8_t x_855; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_unbox(x_854);
lean_dec(x_854);
if (x_855 == 0)
{
lean_object* x_856; 
x_856 = lean_ctor_get(x_853, 1);
lean_inc(x_856);
lean_dec(x_853);
x_844 = x_18;
x_845 = x_856;
goto block_852;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_853, 1);
lean_inc(x_857);
lean_dec(x_853);
x_858 = l_Lean_Expr_mvarId_x21(x_842);
x_859 = lean_array_push(x_18, x_858);
x_844 = x_859;
x_845 = x_857;
goto block_852;
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_842);
lean_dec(x_837);
lean_dec(x_831);
lean_dec(x_739);
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
x_860 = lean_ctor_get(x_853, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_853, 1);
lean_inc(x_861);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_862 = x_853;
} else {
 lean_dec_ref(x_853);
 x_862 = lean_box(0);
}
if (lean_is_scalar(x_862)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_862;
}
lean_ctor_set(x_863, 0, x_860);
lean_ctor_set(x_863, 1, x_861);
return x_863;
}
block_852:
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_846 = l_Lean_Expr_mvarId_x21(x_842);
x_847 = lean_array_push(x_19, x_846);
if (lean_is_scalar(x_837)) {
 x_848 = lean_alloc_ctor(0, 8, 2);
} else {
 x_848 = x_837;
}
lean_ctor_set(x_848, 0, x_11);
lean_ctor_set(x_848, 1, x_12);
lean_ctor_set(x_848, 2, x_13);
lean_ctor_set(x_848, 3, x_15);
lean_ctor_set(x_848, 4, x_16);
lean_ctor_set(x_848, 5, x_17);
lean_ctor_set(x_848, 6, x_844);
lean_ctor_set(x_848, 7, x_847);
lean_ctor_set_uint8(x_848, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_848, sizeof(void*)*8 + 1, x_731);
lean_inc(x_842);
x_849 = l_Lean_mkApp(x_2, x_842);
x_850 = lean_expr_instantiate1(x_831, x_842);
lean_dec(x_842);
lean_dec(x_831);
x_1 = x_848;
x_2 = x_849;
x_3 = x_850;
x_8 = x_739;
x_10 = x_845;
goto _start;
}
}
else
{
lean_object* x_864; lean_object* x_865; 
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_864 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_772, x_4, x_5, x_6, x_7, x_739, x_9, x_773);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_865 = x_1;
} else {
 lean_dec_ref(x_1);
 x_865 = lean_box(0);
}
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_866; lean_object* x_867; uint8_t x_868; 
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_array_get_size(x_12);
x_868 = lean_nat_dec_lt(x_15, x_867);
lean_dec(x_867);
if (x_868 == 0)
{
uint8_t x_869; 
lean_dec(x_865);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_869 = l_Array_isEmpty___rarg(x_16);
if (x_869 == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_732);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_870 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_870, 0, x_829);
x_871 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_872 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_872, 0, x_871);
lean_ctor_set(x_872, 1, x_870);
x_873 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_874 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_873);
x_875 = x_16;
x_876 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_833, x_875);
x_877 = x_876;
x_878 = l_Array_toList___rarg(x_877);
lean_dec(x_877);
x_879 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_878);
x_880 = l_Array_HasRepr___rarg___closed__1;
x_881 = lean_string_append(x_880, x_879);
lean_dec(x_879);
x_882 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_882, 0, x_881);
x_883 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_883, 0, x_882);
x_884 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_884, 0, x_874);
lean_ctor_set(x_884, 1, x_883);
x_885 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_884, x_4, x_5, x_6, x_7, x_739, x_9, x_866);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_885;
}
else
{
lean_object* x_886; uint8_t x_887; 
lean_dec(x_829);
lean_dec(x_16);
x_886 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_887 = l_Lean_checkTraceOption(x_732, x_886);
lean_dec(x_732);
if (x_887 == 0)
{
x_740 = x_866;
goto block_770;
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_inc(x_2);
x_888 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_888, 0, x_2);
x_889 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_886, x_888, x_4, x_5, x_6, x_7, x_739, x_9, x_866);
x_890 = lean_ctor_get(x_889, 1);
lean_inc(x_890);
lean_dec(x_889);
x_740 = x_890;
goto block_770;
}
}
}
else
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_829);
lean_dec(x_732);
lean_dec(x_3);
x_891 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_892 = l___private_Lean_Elab_App_2__elabArg(x_2, x_891, x_830, x_4, x_5, x_6, x_7, x_739, x_9, x_866);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; uint8_t x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_893 = lean_ctor_get(x_892, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_892, 1);
lean_inc(x_894);
lean_dec(x_892);
x_895 = lean_unsigned_to_nat(1u);
x_896 = lean_nat_add(x_15, x_895);
lean_dec(x_15);
x_897 = 1;
if (lean_is_scalar(x_865)) {
 x_898 = lean_alloc_ctor(0, 8, 2);
} else {
 x_898 = x_865;
}
lean_ctor_set(x_898, 0, x_11);
lean_ctor_set(x_898, 1, x_12);
lean_ctor_set(x_898, 2, x_13);
lean_ctor_set(x_898, 3, x_896);
lean_ctor_set(x_898, 4, x_16);
lean_ctor_set(x_898, 5, x_17);
lean_ctor_set(x_898, 6, x_18);
lean_ctor_set(x_898, 7, x_19);
lean_ctor_set_uint8(x_898, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_898, sizeof(void*)*8 + 1, x_897);
lean_inc(x_893);
x_899 = l_Lean_mkApp(x_2, x_893);
x_900 = lean_expr_instantiate1(x_831, x_893);
lean_dec(x_893);
lean_dec(x_831);
x_1 = x_898;
x_2 = x_899;
x_3 = x_900;
x_8 = x_739;
x_10 = x_894;
goto _start;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
lean_dec(x_865);
lean_dec(x_831);
lean_dec(x_739);
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
x_902 = lean_ctor_get(x_892, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_892, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 x_904 = x_892;
} else {
 lean_dec_ref(x_892);
 x_904 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_905 = lean_alloc_ctor(1, 2, 0);
} else {
 x_905 = x_904;
}
lean_ctor_set(x_905, 0, x_902);
lean_ctor_set(x_905, 1, x_903);
return x_905;
}
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
lean_dec(x_865);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_739);
lean_dec(x_732);
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
x_906 = lean_ctor_get(x_864, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_864, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_908 = x_864;
} else {
 lean_dec_ref(x_864);
 x_908 = lean_box(0);
}
if (lean_is_scalar(x_908)) {
 x_909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_909 = x_908;
}
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_907);
return x_909;
}
}
}
case 3:
{
if (x_14 == 0)
{
lean_object* x_910; lean_object* x_911; uint8_t x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_829);
lean_dec(x_772);
lean_dec(x_732);
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
 x_910 = x_1;
} else {
 lean_dec_ref(x_1);
 x_910 = lean_box(0);
}
x_911 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_911, 0, x_830);
x_912 = 1;
x_913 = lean_box(0);
lean_inc(x_6);
x_914 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_911, x_912, x_913, x_6, x_7, x_739, x_9, x_773);
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
x_917 = l_Lean_Expr_mvarId_x21(x_915);
x_918 = lean_array_push(x_17, x_917);
if (lean_is_scalar(x_910)) {
 x_919 = lean_alloc_ctor(0, 8, 2);
} else {
 x_919 = x_910;
}
lean_ctor_set(x_919, 0, x_11);
lean_ctor_set(x_919, 1, x_12);
lean_ctor_set(x_919, 2, x_13);
lean_ctor_set(x_919, 3, x_15);
lean_ctor_set(x_919, 4, x_16);
lean_ctor_set(x_919, 5, x_918);
lean_ctor_set(x_919, 6, x_18);
lean_ctor_set(x_919, 7, x_19);
lean_ctor_set_uint8(x_919, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_919, sizeof(void*)*8 + 1, x_731);
lean_inc(x_915);
x_920 = l_Lean_mkApp(x_2, x_915);
x_921 = lean_expr_instantiate1(x_831, x_915);
lean_dec(x_915);
lean_dec(x_831);
x_1 = x_919;
x_2 = x_920;
x_3 = x_921;
x_8 = x_739;
x_10 = x_916;
goto _start;
}
else
{
uint8_t x_923; 
x_923 = l___private_Lean_Elab_App_8__nextArgIsHole(x_1);
if (x_923 == 0)
{
lean_object* x_924; lean_object* x_925; 
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_924 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_772, x_4, x_5, x_6, x_7, x_739, x_9, x_773);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_925 = x_1;
} else {
 lean_dec_ref(x_1);
 x_925 = lean_box(0);
}
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_926; lean_object* x_927; uint8_t x_928; 
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
lean_dec(x_924);
x_927 = lean_array_get_size(x_12);
x_928 = lean_nat_dec_lt(x_15, x_927);
lean_dec(x_927);
if (x_928 == 0)
{
uint8_t x_929; 
lean_dec(x_925);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_929 = l_Array_isEmpty___rarg(x_16);
if (x_929 == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec(x_732);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_930 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_930, 0, x_829);
x_931 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_932 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_932, 0, x_931);
lean_ctor_set(x_932, 1, x_930);
x_933 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_934 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_934, 0, x_932);
lean_ctor_set(x_934, 1, x_933);
x_935 = x_16;
x_936 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_833, x_935);
x_937 = x_936;
x_938 = l_Array_toList___rarg(x_937);
lean_dec(x_937);
x_939 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_938);
x_940 = l_Array_HasRepr___rarg___closed__1;
x_941 = lean_string_append(x_940, x_939);
lean_dec(x_939);
x_942 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_942, 0, x_941);
x_943 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_943, 0, x_942);
x_944 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_944, 0, x_934);
lean_ctor_set(x_944, 1, x_943);
x_945 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_944, x_4, x_5, x_6, x_7, x_739, x_9, x_926);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_945;
}
else
{
lean_object* x_946; uint8_t x_947; 
lean_dec(x_829);
lean_dec(x_16);
x_946 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_947 = l_Lean_checkTraceOption(x_732, x_946);
lean_dec(x_732);
if (x_947 == 0)
{
x_740 = x_926;
goto block_770;
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_inc(x_2);
x_948 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_948, 0, x_2);
x_949 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_946, x_948, x_4, x_5, x_6, x_7, x_739, x_9, x_926);
x_950 = lean_ctor_get(x_949, 1);
lean_inc(x_950);
lean_dec(x_949);
x_740 = x_950;
goto block_770;
}
}
}
else
{
lean_object* x_951; lean_object* x_952; 
lean_dec(x_829);
lean_dec(x_732);
lean_dec(x_3);
x_951 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_952 = l___private_Lean_Elab_App_2__elabArg(x_2, x_951, x_830, x_4, x_5, x_6, x_7, x_739, x_9, x_926);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; uint8_t x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
x_955 = lean_unsigned_to_nat(1u);
x_956 = lean_nat_add(x_15, x_955);
lean_dec(x_15);
x_957 = 1;
if (lean_is_scalar(x_925)) {
 x_958 = lean_alloc_ctor(0, 8, 2);
} else {
 x_958 = x_925;
}
lean_ctor_set(x_958, 0, x_11);
lean_ctor_set(x_958, 1, x_12);
lean_ctor_set(x_958, 2, x_13);
lean_ctor_set(x_958, 3, x_956);
lean_ctor_set(x_958, 4, x_16);
lean_ctor_set(x_958, 5, x_17);
lean_ctor_set(x_958, 6, x_18);
lean_ctor_set(x_958, 7, x_19);
lean_ctor_set_uint8(x_958, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_958, sizeof(void*)*8 + 1, x_957);
lean_inc(x_953);
x_959 = l_Lean_mkApp(x_2, x_953);
x_960 = lean_expr_instantiate1(x_831, x_953);
lean_dec(x_953);
lean_dec(x_831);
x_1 = x_958;
x_2 = x_959;
x_3 = x_960;
x_8 = x_739;
x_10 = x_954;
goto _start;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_dec(x_925);
lean_dec(x_831);
lean_dec(x_739);
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
x_962 = lean_ctor_get(x_952, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_952, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_964 = x_952;
} else {
 lean_dec_ref(x_952);
 x_964 = lean_box(0);
}
if (lean_is_scalar(x_964)) {
 x_965 = lean_alloc_ctor(1, 2, 0);
} else {
 x_965 = x_964;
}
lean_ctor_set(x_965, 0, x_962);
lean_ctor_set(x_965, 1, x_963);
return x_965;
}
}
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
lean_dec(x_925);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_739);
lean_dec(x_732);
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
x_966 = lean_ctor_get(x_924, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_924, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_968 = x_924;
} else {
 lean_dec_ref(x_924);
 x_968 = lean_box(0);
}
if (lean_is_scalar(x_968)) {
 x_969 = lean_alloc_ctor(1, 2, 0);
} else {
 x_969 = x_968;
}
lean_ctor_set(x_969, 0, x_966);
lean_ctor_set(x_969, 1, x_967);
return x_969;
}
}
else
{
lean_object* x_970; lean_object* x_971; uint8_t x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_829);
lean_dec(x_772);
lean_dec(x_732);
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
 x_970 = x_1;
} else {
 lean_dec_ref(x_1);
 x_970 = lean_box(0);
}
x_971 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_971, 0, x_830);
x_972 = 1;
x_973 = lean_box(0);
lean_inc(x_6);
x_974 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_971, x_972, x_973, x_6, x_7, x_739, x_9, x_773);
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
lean_dec(x_974);
x_977 = lean_unsigned_to_nat(1u);
x_978 = lean_nat_add(x_15, x_977);
lean_dec(x_15);
x_979 = l_Lean_Expr_mvarId_x21(x_975);
x_980 = lean_array_push(x_17, x_979);
if (lean_is_scalar(x_970)) {
 x_981 = lean_alloc_ctor(0, 8, 2);
} else {
 x_981 = x_970;
}
lean_ctor_set(x_981, 0, x_11);
lean_ctor_set(x_981, 1, x_12);
lean_ctor_set(x_981, 2, x_13);
lean_ctor_set(x_981, 3, x_978);
lean_ctor_set(x_981, 4, x_16);
lean_ctor_set(x_981, 5, x_980);
lean_ctor_set(x_981, 6, x_18);
lean_ctor_set(x_981, 7, x_19);
lean_ctor_set_uint8(x_981, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_981, sizeof(void*)*8 + 1, x_731);
lean_inc(x_975);
x_982 = l_Lean_mkApp(x_2, x_975);
x_983 = lean_expr_instantiate1(x_831, x_975);
lean_dec(x_975);
lean_dec(x_831);
x_1 = x_981;
x_2 = x_982;
x_3 = x_983;
x_8 = x_739;
x_10 = x_976;
goto _start;
}
}
}
default: 
{
lean_object* x_985; lean_object* x_986; 
lean_dec(x_836);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_985 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_772, x_4, x_5, x_6, x_7, x_739, x_9, x_773);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_986 = x_1;
} else {
 lean_dec_ref(x_1);
 x_986 = lean_box(0);
}
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_987; uint8_t x_988; lean_object* x_989; lean_object* x_990; uint8_t x_991; 
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec(x_985);
x_988 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_986)) {
 x_989 = lean_alloc_ctor(0, 8, 2);
} else {
 x_989 = x_986;
}
lean_ctor_set(x_989, 0, x_11);
lean_ctor_set(x_989, 1, x_12);
lean_ctor_set(x_989, 2, x_13);
lean_ctor_set(x_989, 3, x_15);
lean_ctor_set(x_989, 4, x_16);
lean_ctor_set(x_989, 5, x_17);
lean_ctor_set(x_989, 6, x_18);
lean_ctor_set(x_989, 7, x_19);
lean_ctor_set_uint8(x_989, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_989, sizeof(void*)*8 + 1, x_988);
x_990 = lean_array_get_size(x_12);
x_991 = lean_nat_dec_lt(x_15, x_990);
lean_dec(x_990);
if (x_991 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_992; 
x_992 = l_Lean_Expr_getOptParamDefault_x3f(x_830);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; 
x_993 = l_Lean_Expr_getAutoParamTactic_x3f(x_830);
if (lean_obj_tag(x_993) == 0)
{
uint8_t x_994; 
lean_dec(x_989);
lean_dec(x_831);
lean_dec(x_830);
x_994 = l_Array_isEmpty___rarg(x_16);
if (x_994 == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_732);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_995 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_995, 0, x_829);
x_996 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_997 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_997, 0, x_996);
lean_ctor_set(x_997, 1, x_995);
x_998 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_999 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_999, 0, x_997);
lean_ctor_set(x_999, 1, x_998);
x_1000 = x_16;
x_1001 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_833, x_1000);
x_1002 = x_1001;
x_1003 = l_Array_toList___rarg(x_1002);
lean_dec(x_1002);
x_1004 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1003);
x_1005 = l_Array_HasRepr___rarg___closed__1;
x_1006 = lean_string_append(x_1005, x_1004);
lean_dec(x_1004);
x_1007 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1007, 0, x_1006);
x_1008 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1008, 0, x_1007);
x_1009 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1009, 0, x_999);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1009, x_4, x_5, x_6, x_7, x_739, x_9, x_987);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1010;
}
else
{
lean_object* x_1011; uint8_t x_1012; 
lean_dec(x_829);
lean_dec(x_16);
x_1011 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_1012 = l_Lean_checkTraceOption(x_732, x_1011);
lean_dec(x_732);
if (x_1012 == 0)
{
x_740 = x_987;
goto block_770;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
lean_inc(x_2);
x_1013 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1013, 0, x_2);
x_1014 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1011, x_1013, x_4, x_5, x_6, x_7, x_739, x_9, x_987);
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
lean_dec(x_1014);
x_740 = x_1015;
goto block_770;
}
}
}
else
{
lean_object* x_1016; 
lean_dec(x_829);
lean_dec(x_732);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1016 = lean_ctor_get(x_993, 0);
lean_inc(x_1016);
lean_dec(x_993);
if (lean_obj_tag(x_1016) == 4)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
lean_dec(x_1016);
x_1018 = lean_st_ref_get(x_9, x_987);
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec(x_1018);
x_1021 = lean_ctor_get(x_1019, 0);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = l___private_Lean_Elab_Util_2__evalSyntaxConstantUnsafe(x_1021, x_1017);
if (lean_obj_tag(x_1022) == 0)
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_989);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_11);
lean_dec(x_2);
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
lean_dec(x_1022);
x_1024 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1024, 0, x_1023);
x_1025 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1025, 0, x_1024);
x_1026 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1025, x_4, x_5, x_6, x_7, x_739, x_9, x_1020);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1026;
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1027 = lean_ctor_get(x_1022, 0);
lean_inc(x_1027);
lean_dec(x_1022);
x_1028 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_739, x_9, x_1020);
x_1029 = lean_ctor_get(x_1028, 1);
lean_inc(x_1029);
lean_dec(x_1028);
x_1030 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1029);
x_1031 = lean_ctor_get(x_1030, 1);
lean_inc(x_1031);
lean_dec(x_1030);
x_1032 = l_Lean_Syntax_getArgs(x_1027);
lean_dec(x_1027);
x_1033 = l_Array_empty___closed__1;
x_1034 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1032, x_1032, x_833, x_1033);
lean_dec(x_1032);
x_1035 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_1036 = lean_array_push(x_1034, x_1035);
x_1037 = l_Lean_nullKind___closed__2;
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1037);
lean_ctor_set(x_1038, 1, x_1036);
x_1039 = lean_array_push(x_1033, x_1038);
x_1040 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1040, 0, x_1037);
lean_ctor_set(x_1040, 1, x_1039);
x_1041 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1042 = lean_array_push(x_1041, x_1040);
x_1043 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16;
x_1044 = lean_array_push(x_1042, x_1043);
x_1045 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_1046 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_1044);
x_1047 = lean_array_push(x_1033, x_1046);
x_1048 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_1049 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_1047);
x_1050 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15;
x_1051 = lean_array_push(x_1050, x_1049);
x_1052 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1053 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1051);
x_1054 = l_Lean_Syntax_copyInfo(x_1053, x_11);
lean_dec(x_11);
x_1055 = l_Lean_Expr_getAppNumArgsAux___main(x_830, x_833);
x_1056 = lean_nat_sub(x_1055, x_833);
lean_dec(x_1055);
x_1057 = lean_unsigned_to_nat(1u);
x_1058 = lean_nat_sub(x_1056, x_1057);
lean_dec(x_1056);
x_1059 = l_Lean_Expr_getRevArg_x21___main(x_830, x_1058);
lean_dec(x_830);
x_1060 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1060, 0, x_1054);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1061 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1060, x_1059, x_4, x_5, x_6, x_7, x_739, x_9, x_1031);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
lean_inc(x_1062);
x_1064 = l_Lean_mkApp(x_2, x_1062);
x_1065 = lean_expr_instantiate1(x_831, x_1062);
lean_dec(x_1062);
lean_dec(x_831);
x_1 = x_989;
x_2 = x_1064;
x_3 = x_1065;
x_8 = x_739;
x_10 = x_1063;
goto _start;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_989);
lean_dec(x_831);
lean_dec(x_739);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1067 = lean_ctor_get(x_1061, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1061, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1061)) {
 lean_ctor_release(x_1061, 0);
 lean_ctor_release(x_1061, 1);
 x_1069 = x_1061;
} else {
 lean_dec_ref(x_1061);
 x_1069 = lean_box(0);
}
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_1067);
lean_ctor_set(x_1070, 1, x_1068);
return x_1070;
}
}
}
else
{
lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_1016);
lean_dec(x_989);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_11);
lean_dec(x_2);
x_1071 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12;
x_1072 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1071, x_4, x_5, x_6, x_7, x_739, x_9, x_987);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1072;
}
}
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_732);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1073 = lean_ctor_get(x_992, 0);
lean_inc(x_1073);
lean_dec(x_992);
lean_inc(x_1073);
x_1074 = l_Lean_mkApp(x_2, x_1073);
x_1075 = lean_expr_instantiate1(x_831, x_1073);
lean_dec(x_1073);
lean_dec(x_831);
x_1 = x_989;
x_2 = x_1074;
x_3 = x_1075;
x_8 = x_739;
x_10 = x_987;
goto _start;
}
}
else
{
uint8_t x_1077; 
lean_dec(x_989);
lean_dec(x_831);
lean_dec(x_830);
x_1077 = l_Array_isEmpty___rarg(x_16);
if (x_1077 == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_732);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1078 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1078, 0, x_829);
x_1079 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6;
x_1080 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1080, 0, x_1079);
lean_ctor_set(x_1080, 1, x_1078);
x_1081 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9;
x_1082 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1082, 0, x_1080);
lean_ctor_set(x_1082, 1, x_1081);
x_1083 = x_16;
x_1084 = l_Array_umapMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__4(x_833, x_1083);
x_1085 = x_1084;
x_1086 = l_Array_toList___rarg(x_1085);
lean_dec(x_1085);
x_1087 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1086);
x_1088 = l_Array_HasRepr___rarg___closed__1;
x_1089 = lean_string_append(x_1088, x_1087);
lean_dec(x_1087);
x_1090 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1090, 0, x_1089);
x_1091 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1091, 0, x_1090);
x_1092 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1092, 0, x_1082);
lean_ctor_set(x_1092, 1, x_1091);
x_1093 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1092, x_4, x_5, x_6, x_7, x_739, x_9, x_987);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1093;
}
else
{
lean_object* x_1094; uint8_t x_1095; 
lean_dec(x_829);
lean_dec(x_16);
x_1094 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_1095 = l_Lean_checkTraceOption(x_732, x_1094);
lean_dec(x_732);
if (x_1095 == 0)
{
x_740 = x_987;
goto block_770;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
lean_inc(x_2);
x_1096 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1096, 0, x_2);
x_1097 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1094, x_1096, x_4, x_5, x_6, x_7, x_739, x_9, x_987);
x_1098 = lean_ctor_get(x_1097, 1);
lean_inc(x_1098);
lean_dec(x_1097);
x_740 = x_1098;
goto block_770;
}
}
}
}
else
{
lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_989);
lean_dec(x_829);
lean_dec(x_732);
lean_dec(x_3);
x_1099 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1100 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1099, x_830, x_4, x_5, x_6, x_7, x_739, x_9, x_987);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = lean_unsigned_to_nat(1u);
x_1104 = lean_nat_add(x_15, x_1103);
lean_dec(x_15);
x_1105 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1105, 0, x_11);
lean_ctor_set(x_1105, 1, x_12);
lean_ctor_set(x_1105, 2, x_13);
lean_ctor_set(x_1105, 3, x_1104);
lean_ctor_set(x_1105, 4, x_16);
lean_ctor_set(x_1105, 5, x_17);
lean_ctor_set(x_1105, 6, x_18);
lean_ctor_set(x_1105, 7, x_19);
lean_ctor_set_uint8(x_1105, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1105, sizeof(void*)*8 + 1, x_988);
lean_inc(x_1101);
x_1106 = l_Lean_mkApp(x_2, x_1101);
x_1107 = lean_expr_instantiate1(x_831, x_1101);
lean_dec(x_1101);
lean_dec(x_831);
x_1 = x_1105;
x_2 = x_1106;
x_3 = x_1107;
x_8 = x_739;
x_10 = x_1102;
goto _start;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_831);
lean_dec(x_739);
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
x_1109 = lean_ctor_get(x_1100, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1100, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 x_1111 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1111 = lean_box(0);
}
if (lean_is_scalar(x_1111)) {
 x_1112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1112 = x_1111;
}
lean_ctor_set(x_1112, 0, x_1109);
lean_ctor_set(x_1112, 1, x_1110);
return x_1112;
}
}
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_986);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_739);
lean_dec(x_732);
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
x_1113 = lean_ctor_get(x_985, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_985, 1);
lean_inc(x_1114);
if (lean_is_exclusive(x_985)) {
 lean_ctor_release(x_985, 0);
 lean_ctor_release(x_985, 1);
 x_1115 = x_985;
} else {
 lean_dec_ref(x_985);
 x_1115 = lean_box(0);
}
if (lean_is_scalar(x_1115)) {
 x_1116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1116 = x_1115;
}
lean_ctor_set(x_1116, 0, x_1113);
lean_ctor_set(x_1116, 1, x_1114);
return x_1116;
}
}
}
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec(x_829);
lean_dec(x_732);
lean_dec(x_3);
x_1117 = lean_ctor_get(x_834, 0);
lean_inc(x_1117);
lean_dec(x_834);
x_1118 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1119 = lean_array_get(x_1118, x_16, x_1117);
x_1120 = l_Array_eraseIdx___rarg(x_16, x_1117);
lean_dec(x_1117);
x_1121 = lean_ctor_get(x_1119, 1);
lean_inc(x_1121);
lean_dec(x_1119);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1122 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1121, x_830, x_4, x_5, x_6, x_7, x_739, x_9, x_773);
if (lean_obj_tag(x_1122) == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
lean_dec(x_1122);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1125 = l___private_Lean_Elab_App_7__propagateExpectedType(x_1, x_772, x_4, x_5, x_6, x_7, x_739, x_9, x_1124);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_1126 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1126 = lean_box(0);
}
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
lean_dec(x_1125);
x_1128 = 1;
if (lean_is_scalar(x_1126)) {
 x_1129 = lean_alloc_ctor(0, 8, 2);
} else {
 x_1129 = x_1126;
}
lean_ctor_set(x_1129, 0, x_11);
lean_ctor_set(x_1129, 1, x_12);
lean_ctor_set(x_1129, 2, x_13);
lean_ctor_set(x_1129, 3, x_15);
lean_ctor_set(x_1129, 4, x_1120);
lean_ctor_set(x_1129, 5, x_17);
lean_ctor_set(x_1129, 6, x_18);
lean_ctor_set(x_1129, 7, x_19);
lean_ctor_set_uint8(x_1129, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1129, sizeof(void*)*8 + 1, x_1128);
lean_inc(x_1123);
x_1130 = l_Lean_mkApp(x_2, x_1123);
x_1131 = lean_expr_instantiate1(x_831, x_1123);
lean_dec(x_1123);
lean_dec(x_831);
x_1 = x_1129;
x_2 = x_1130;
x_3 = x_1131;
x_8 = x_739;
x_10 = x_1127;
goto _start;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
lean_dec(x_1126);
lean_dec(x_1123);
lean_dec(x_1120);
lean_dec(x_831);
lean_dec(x_739);
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
x_1133 = lean_ctor_get(x_1125, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1125, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1135 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1135 = lean_box(0);
}
if (lean_is_scalar(x_1135)) {
 x_1136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1136 = x_1135;
}
lean_ctor_set(x_1136, 0, x_1133);
lean_ctor_set(x_1136, 1, x_1134);
return x_1136;
}
}
else
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1120);
lean_dec(x_831);
lean_dec(x_772);
lean_dec(x_739);
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
x_1137 = lean_ctor_get(x_1122, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1122, 1);
lean_inc(x_1138);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 x_1139 = x_1122;
} else {
 lean_dec_ref(x_1122);
 x_1139 = lean_box(0);
}
if (lean_is_scalar(x_1139)) {
 x_1140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1140 = x_1139;
}
lean_ctor_set(x_1140, 0, x_1137);
lean_ctor_set(x_1140, 1, x_1138);
return x_1140;
}
}
}
else
{
lean_object* x_1141; 
lean_dec(x_1);
x_1141 = lean_box(0);
x_774 = x_1141;
goto block_828;
}
block_828:
{
lean_object* x_775; uint8_t x_818; 
lean_dec(x_774);
x_818 = l_Array_isEmpty___rarg(x_16);
if (x_818 == 0)
{
lean_object* x_819; 
lean_dec(x_732);
lean_dec(x_3);
x_819 = lean_box(0);
x_775 = x_819;
goto block_817;
}
else
{
lean_object* x_820; uint8_t x_821; 
x_820 = lean_array_get_size(x_12);
x_821 = lean_nat_dec_eq(x_15, x_820);
lean_dec(x_820);
if (x_821 == 0)
{
lean_object* x_822; 
lean_dec(x_732);
lean_dec(x_3);
x_822 = lean_box(0);
x_775 = x_822;
goto block_817;
}
else
{
lean_object* x_823; uint8_t x_824; 
lean_dec(x_772);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_823 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3;
x_824 = l_Lean_checkTraceOption(x_732, x_823);
lean_dec(x_732);
if (x_824 == 0)
{
x_740 = x_773;
goto block_770;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_inc(x_2);
x_825 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_825, 0, x_2);
x_826 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_823, x_825, x_4, x_5, x_6, x_7, x_739, x_9, x_773);
x_827 = lean_ctor_get(x_826, 1);
lean_inc(x_827);
lean_dec(x_826);
x_740 = x_827;
goto block_770;
}
}
}
block_817:
{
lean_object* x_776; lean_object* x_777; 
lean_dec(x_775);
x_776 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_777 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_776, x_4, x_5, x_6, x_7, x_739, x_9, x_773);
lean_dec(x_17);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; uint8_t x_779; lean_object* x_780; lean_object* x_781; 
x_778 = lean_ctor_get(x_777, 1);
lean_inc(x_778);
lean_dec(x_777);
x_779 = 1;
x_780 = lean_box(0);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_781 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_779, x_780, x_4, x_5, x_6, x_7, x_739, x_9, x_778);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_782 = lean_ctor_get(x_781, 1);
lean_inc(x_782);
lean_dec(x_781);
x_783 = l_Array_empty___closed__1;
x_784 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_784, 0, x_11);
lean_ctor_set(x_784, 1, x_12);
lean_ctor_set(x_784, 2, x_13);
lean_ctor_set(x_784, 3, x_15);
lean_ctor_set(x_784, 4, x_16);
lean_ctor_set(x_784, 5, x_783);
lean_ctor_set(x_784, 6, x_18);
lean_ctor_set(x_784, 7, x_19);
lean_ctor_set_uint8(x_784, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_784, sizeof(void*)*8 + 1, x_731);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
x_785 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_16__useImplicitLambda_x3f___spec__1(x_772, x_4, x_5, x_6, x_7, x_739, x_9, x_782);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
if (lean_obj_tag(x_786) == 7)
{
lean_object* x_787; 
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
lean_dec(x_785);
x_1 = x_784;
x_3 = x_786;
x_8 = x_739;
x_10 = x_787;
goto _start;
}
else
{
lean_object* x_789; lean_object* x_790; 
x_789 = lean_ctor_get(x_785, 1);
lean_inc(x_789);
lean_dec(x_785);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_790 = l___private_Lean_Elab_App_3__tryCoeFun(x_786, x_2, x_4, x_5, x_6, x_7, x_739, x_9, x_789);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
lean_dec(x_790);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_791);
x_793 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_791, x_4, x_5, x_6, x_7, x_739, x_9, x_792);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_1 = x_784;
x_2 = x_791;
x_3 = x_794;
x_8 = x_739;
x_10 = x_795;
goto _start;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_791);
lean_dec(x_784);
lean_dec(x_739);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_797 = lean_ctor_get(x_793, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_793, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_799 = x_793;
} else {
 lean_dec_ref(x_793);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_797);
lean_ctor_set(x_800, 1, x_798);
return x_800;
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_784);
lean_dec(x_739);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_801 = lean_ctor_get(x_790, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_790, 1);
lean_inc(x_802);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_803 = x_790;
} else {
 lean_dec_ref(x_790);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(1, 2, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_801);
lean_ctor_set(x_804, 1, x_802);
return x_804;
}
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_784);
lean_dec(x_739);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_805 = lean_ctor_get(x_785, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_785, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_807 = x_785;
} else {
 lean_dec_ref(x_785);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 2, 0);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_805);
lean_ctor_set(x_808, 1, x_806);
return x_808;
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_772);
lean_dec(x_739);
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
x_809 = lean_ctor_get(x_781, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_781, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_811 = x_781;
} else {
 lean_dec_ref(x_781);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_809);
lean_ctor_set(x_812, 1, x_810);
return x_812;
}
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_772);
lean_dec(x_739);
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
x_813 = lean_ctor_get(x_777, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_777, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 lean_ctor_release(x_777, 1);
 x_815 = x_777;
} else {
 lean_dec_ref(x_777);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
}
}
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
lean_dec(x_739);
lean_dec(x_732);
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
x_1142 = lean_ctor_get(x_771, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_771, 1);
lean_inc(x_1143);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_1144 = x_771;
} else {
 lean_dec_ref(x_771);
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
block_770:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_3);
x_741 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_742 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_741, x_4, x_5, x_6, x_7, x_739, x_9, x_740);
lean_dec(x_17);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec(x_742);
lean_inc(x_2);
x_744 = l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1(x_2, x_11, x_19, x_741, x_4, x_5, x_6, x_7, x_739, x_9, x_743);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_745 = lean_ctor_get(x_744, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 x_746 = x_744;
} else {
 lean_dec_ref(x_744);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_2);
lean_ctor_set(x_747, 1, x_745);
return x_747;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_739);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_748 = lean_ctor_get(x_742, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_742, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_750 = x_742;
} else {
 lean_dec_ref(x_742);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
}
else
{
lean_object* x_752; lean_object* x_753; 
x_752 = lean_ctor_get(x_13, 0);
lean_inc(x_752);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
x_753 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_752, x_3, x_4, x_5, x_6, x_7, x_739, x_9, x_740);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
lean_dec(x_753);
x_755 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_739);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_756 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_755, x_4, x_5, x_6, x_7, x_739, x_9, x_754);
lean_dec(x_17);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_757 = lean_ctor_get(x_756, 1);
lean_inc(x_757);
lean_dec(x_756);
lean_inc(x_2);
x_758 = l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2(x_2, x_11, x_19, x_755, x_4, x_5, x_6, x_7, x_739, x_9, x_757);
lean_dec(x_9);
lean_dec(x_739);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_759 = lean_ctor_get(x_758, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_760 = x_758;
} else {
 lean_dec_ref(x_758);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(0, 2, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_2);
lean_ctor_set(x_761, 1, x_759);
return x_761;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_739);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_762 = lean_ctor_get(x_756, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_756, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_764 = x_756;
} else {
 lean_dec_ref(x_756);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_739);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_766 = lean_ctor_get(x_753, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_753, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_768 = x_753;
} else {
 lean_dec_ref(x_753);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_768)) {
 x_769 = lean_alloc_ctor(1, 2, 0);
} else {
 x_769 = x_768;
}
lean_ctor_set(x_769, 0, x_766);
lean_ctor_set(x_769, 1, x_767);
return x_769;
}
}
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_9__elabAppArgsAux___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_9__elabAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_9__elabAppArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgs___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgs___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgs___closed__6;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgs___closed__8;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_10__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
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
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
x_54 = l___private_Lean_Elab_App_10__elabAppArgs___closed__2;
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
x_58 = l___private_Lean_Elab_App_10__elabAppArgs___closed__7;
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
x_65 = l___private_Lean_Elab_App_10__elabAppArgs___closed__9;
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
x_28 = l___private_Lean_Elab_App_9__elabAppArgsAux___main(x_27, x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
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
x_41 = l___private_Lean_Elab_App_9__elabAppArgsAux___main(x_40, x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
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
x_51 = l___private_Lean_Elab_App_9__elabAppArgsAux___main(x_50, x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
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
lean_object* l___private_Lean_Elab_App_10__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Elab_App_10__elabAppArgs(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_11__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Elab_App_11__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_11__throwLValError___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_11__throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_12__findMethod_x3f___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_1, x_8, x_2);
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
lean_object* l___private_Lean_Elab_App_12__findMethod_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_12__findMethod_x3f___main___spec__1(x_1, x_3, x_10, x_11);
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
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_12__findMethod_x3f___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_12__findMethod_x3f___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_12__findMethod_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_49 = l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
x_50 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
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
x_36 = l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
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
x_55 = l___private_Lean_Elab_App_13__resolveLValAux___closed__18;
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
x_79 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_72);
lean_dec(x_61);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_62);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_90 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_89, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
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
x_99 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_72);
lean_dec(x_61);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_62);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_110 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_109, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
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
x_122 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_61);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_62);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_133 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
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
x_143 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_61);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_62);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_154 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_153, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
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
x_174 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_free_object(x_167);
lean_dec(x_61);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_62);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_178 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_185 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_184, x_4, x_5, x_6, x_7, x_8, x_9, x_170);
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
x_194 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_free_object(x_167);
lean_dec(x_61);
x_195 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_195, 0, x_62);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_205 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_204, x_4, x_5, x_6, x_7, x_8, x_9, x_170);
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
x_217 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_61);
x_218 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_218, 0, x_62);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_221 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_228 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_227, x_4, x_5, x_6, x_7, x_8, x_9, x_213);
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
x_238 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_61);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_62);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_242 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_249 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_248, x_4, x_5, x_6, x_7, x_8, x_9, x_213);
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
x_274 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_262, x_61, x_265);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_270);
lean_dec(x_61);
x_275 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_275, 0, x_62);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_275);
x_277 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_278 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_285 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_284, x_4, x_5, x_6, x_7, x_8, x_9, x_269);
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
x_295 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_262, x_61, x_265);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_270);
lean_dec(x_61);
x_296 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_296, 0, x_62);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_298 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_299 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_306 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_305, x_4, x_5, x_6, x_7, x_8, x_9, x_269);
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
x_326 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_262, x_61, x_316);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_322);
lean_dec(x_61);
x_327 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_327, 0, x_62);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_327);
x_329 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_330 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_337 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_336, x_4, x_5, x_6, x_7, x_8, x_9, x_321);
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
x_347 = l___private_Lean_Elab_App_12__findMethod_x3f___main(x_262, x_61, x_316);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_322);
lean_dec(x_61);
x_348 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_348, 0, x_62);
x_349 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_350 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_351 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_352 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
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
x_358 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_357, x_4, x_5, x_6, x_7, x_8, x_9, x_321);
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
x_377 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
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
x_381 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_384, x_4, x_5, x_6, x_7, x_8, x_9, x_375);
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
x_390 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_391 = lean_name_mk_string(x_370, x_390);
lean_inc(x_391);
x_392 = lean_environment_find(x_389, x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_371);
x_393 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_394 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
x_396 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_397 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_398 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_397, x_4, x_5, x_6, x_7, x_8, x_9, x_388);
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
x_12 = l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
x_13 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
x_15 = l___private_Lean_Elab_App_11__throwLValError___rarg(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_13__resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_14__consumeImplicits___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_App_14__consumeImplicits___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_14__consumeImplicits___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_14__consumeImplicits(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_14__consumeImplicits___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_14__consumeImplicits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_14__consumeImplicits(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
x_15 = l_Lean_Elab_logException___at___private_Lean_Elab_Term_8__exceptionToSorry___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_App_14__consumeImplicits___main(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_20 = l___private_Lean_Elab_App_13__resolveLValAux(x_16, x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
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
x_32 = l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(x_4, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
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
x_57 = l___private_Lean_Elab_App_13__resolveLValAux(x_53, x_54, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
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
x_69 = l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(x_4, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
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
x_14 = l___private_Lean_Elab_App_15__resolveLValLoop___main(x_2, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
x_25 = l___private_Lean_Elab_App_10__elabAppArgs(x_15, x_21, x_23, x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
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
x_17 = l___private_Lean_Elab_App_18__addLValArg___main___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_App_18__addLValArg___main___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_App_18__addLValArg___main___closed__9;
x_24 = lean_alloc_ctor(10, 2, 0);
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
x_14 = l___private_Lean_Elab_App_10__elabAppArgs(x_5, x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_17 = l___private_Lean_Elab_App_16__resolveLVal(x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_25 = l___private_Lean_Elab_App_17__mkBaseProjections(x_22, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
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
x_35 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
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
x_42 = l___private_Lean_Elab_App_10__elabAppArgs(x_31, x_38, x_40, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
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
x_51 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
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
x_56 = l___private_Lean_Elab_App_10__elabAppArgs(x_31, x_54, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
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
x_81 = l___private_Lean_Elab_App_17__mkBaseProjections(x_77, x_78, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
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
x_95 = l___private_Lean_Elab_App_10__elabAppArgs(x_86, x_93, x_91, x_92, x_94, x_7, x_8, x_9, x_10, x_11, x_12, x_87);
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
x_107 = l___private_Lean_Elab_App_18__addLValArg___main(x_77, x_79, x_82, x_2, x_106, x_1, x_104, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
lean_dec(x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l___private_Lean_Elab_App_10__elabAppArgs(x_86, x_1, x_108, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_109);
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
x_138 = l___private_Lean_Elab_App_10__elabAppArgs(x_129, x_136, x_134, x_135, x_137, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
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
x_150 = l___private_Lean_Elab_App_18__addLValArg___main(x_77, x_79, x_76, x_2, x_149, x_1, x_147, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
lean_dec(x_147);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l___private_Lean_Elab_App_10__elabAppArgs(x_129, x_1, x_151, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_152);
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
x_178 = l___private_Lean_Elab_App_10__elabAppArgs(x_170, x_176, x_174, x_175, x_177, x_7, x_8, x_9, x_10, x_11, x_12, x_166);
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
x_190 = l___private_Lean_Elab_App_18__addLValArg___main(x_168, x_169, x_167, x_2, x_189, x_1, x_187, x_7, x_8, x_9, x_10, x_11, x_12, x_188);
lean_dec(x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Elab_App_10__elabAppArgs(x_170, x_1, x_191, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_192);
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
x_212 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_205);
x_215 = l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2;
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
x_223 = l___private_Lean_Elab_App_10__elabAppArgs(x_208, x_219, x_221, x_220, x_222, x_7, x_8, x_9, x_10, x_11, x_12, x_209);
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
x_232 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
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
x_238 = l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2;
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
x_243 = l___private_Lean_Elab_App_10__elabAppArgs(x_208, x_241, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_242);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_21 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(x_20);
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
x_52 = l___private_Lean_Elab_App_20__elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_21 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(x_20);
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
x_52 = l___private_Lean_Elab_App_20__elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
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
lean_object* l___private_Lean_Elab_App_21__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_54 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_57 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_56, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_67 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_70 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_69, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_16);
return x_78;
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l___private_Lean_Elab_App_21__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
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
uint8_t x_16; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
lean_inc(x_1);
x_381 = l_Lean_Syntax_getKind(x_1);
x_382 = l_Lean_choiceKind;
x_383 = lean_name_eq(x_381, x_382);
lean_dec(x_381);
if (x_383 == 0)
{
uint8_t x_384; uint8_t x_1180; lean_object* x_1594; uint8_t x_1595; 
x_1594 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
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
x_803 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
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
x_407 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
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
x_398 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_15);
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
x_402 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_15);
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
x_418 = l___private_Lean_Elab_Term_12__isExplicit___closed__2;
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
x_493 = l___private_Lean_Elab_App_20__elabAppLVals(x_491, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_492);
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
x_571 = l___private_Lean_Elab_App_20__elabAppLVals(x_569, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_570);
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
x_649 = l___private_Lean_Elab_App_20__elabAppLVals(x_647, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_648);
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
x_797 = l___private_Lean_Elab_App_21__elabAppFnId(x_426, x_795, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_796);
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
x_811 = l___private_Lean_Elab_App_21__elabAppFnId(x_1, x_810, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_881 = l___private_Lean_Elab_App_20__elabAppLVals(x_879, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_880);
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
x_959 = l___private_Lean_Elab_App_20__elabAppLVals(x_957, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_958);
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
x_1037 = l___private_Lean_Elab_App_20__elabAppLVals(x_1035, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1036);
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
x_1177 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__8;
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
x_1181 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__10;
lean_inc(x_1);
x_1182 = l_Lean_Syntax_isOfKind(x_1, x_1181);
if (x_1182 == 0)
{
lean_object* x_1183; uint8_t x_1184; 
x_1183 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
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
x_1194 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
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
x_1279 = l___private_Lean_Elab_App_20__elabAppLVals(x_1277, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1278);
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
x_1357 = l___private_Lean_Elab_App_20__elabAppLVals(x_1355, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1356);
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
x_1435 = l___private_Lean_Elab_App_20__elabAppLVals(x_1433, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1434);
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
x_1578 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(x_1577);
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
x_1605 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1601, x_1604, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_1618 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1601, x_1617, x_8, x_1616, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_82 = l___private_Lean_Elab_App_20__elabAppLVals(x_80, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
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
x_160 = l___private_Lean_Elab_App_20__elabAppLVals(x_158, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_159);
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
x_238 = l___private_Lean_Elab_App_20__elabAppLVals(x_236, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_237);
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
x_378 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__3;
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
uint8_t l___private_Lean_Elab_App_23__isSuccess(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_App_23__isSuccess___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_23__isSuccess(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_24__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_App_23__isSuccess(x_7);
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
lean_object* l___private_Lean_Elab_App_24__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Lean_Elab_App_24__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_App_25__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_25__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg(x_6, x_7, x_8);
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
x_23 = l___private_Lean_Elab_App_25__toMessageData___closed__1;
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
x_49 = l___private_Lean_Elab_App_25__toMessageData___closed__1;
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_25__toMessageData___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_25__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_25__toMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_26__toMessageList(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_App_26__toMessageList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_App_26__toMessageList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_27__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_33 = l___private_Lean_Elab_App_25__toMessageData(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* _init_l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_27__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_27__mergeFailures___spec__1), 9, 2);
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
x_16 = l___private_Lean_Elab_App_26__toMessageList(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__3;
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
lean_object* l___private_Lean_Elab_App_27__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_27__mergeFailures___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_28__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Lean_Elab_App_28__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_28__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_28__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_28__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_28__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_28__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Array_filterAux___main___at___private_Lean_Elab_App_24__getSuccess___spec__1(x_16, x_21, x_21);
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
x_31 = l___private_Lean_Elab_App_27__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
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
x_40 = l___private_Lean_Elab_App_27__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_39, x_10, x_17);
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
x_44 = l_Array_umapMAux___main___at___private_Lean_Elab_App_28__elabAppAux___spec__1(x_41, x_42, x_21, x_43);
x_45 = x_44;
x_46 = l___private_Lean_Elab_App_26__toMessageList(x_45);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_App_28__elabAppAux___closed__3;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
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
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_46 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_44, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_19 = l___private_Lean_Elab_App_28__elabAppAux(x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
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
lean_object* l___private_Lean_Elab_App_29__elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_App_28__elabAppAux(x_1, x_10, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_77 = l___private_Lean_Elab_Term_12__isExplicit___closed__2;
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
x_52 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
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
x_63 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
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
x_73 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_71, x_72, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_13);
x_74 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_74;
}
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_13);
x_75 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_75;
}
block_47:
{
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = 0;
x_17 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_23 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_21, x_22, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_30 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_28, x_29, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_37 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_35, x_36, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_43 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_41, x_42, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_43;
}
else
{
uint8_t x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_13);
x_44 = 1;
x_45 = 0;
x_46 = l___private_Lean_Elab_Term_19__elabTermAux___main(x_2, x_44, x_45, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_Term_12__isExplicit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_29__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_30__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1;
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
l___private_Lean_Elab_App_3__tryCoeFun___closed__1 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__1);
l___private_Lean_Elab_App_3__tryCoeFun___closed__2 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__2);
l___private_Lean_Elab_App_3__tryCoeFun___closed__3 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__3);
l___private_Lean_Elab_App_3__tryCoeFun___closed__4 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__4);
l___private_Lean_Elab_App_3__tryCoeFun___closed__5 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__5);
l___private_Lean_Elab_App_3__tryCoeFun___closed__6 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__6);
l___private_Lean_Elab_App_3__tryCoeFun___closed__7 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__7);
l___private_Lean_Elab_App_3__tryCoeFun___closed__8 = _init_l___private_Lean_Elab_App_3__tryCoeFun___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_3__tryCoeFun___closed__8);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__1);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__2 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__2);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__3);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__4 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__4);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__5 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__5);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__6);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__7 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__7);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__8 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__8);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__9);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__10 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__10);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__11 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__11);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__12);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__13 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__13);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__14 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__14);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__15);
l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16 = _init_l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_9__elabAppArgsAux___main___closed__16);
l___private_Lean_Elab_App_10__elabAppArgs___closed__1 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__1);
l___private_Lean_Elab_App_10__elabAppArgs___closed__2 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__2);
l___private_Lean_Elab_App_10__elabAppArgs___closed__3 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__3);
l___private_Lean_Elab_App_10__elabAppArgs___closed__4 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__4);
l___private_Lean_Elab_App_10__elabAppArgs___closed__5 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__5);
l___private_Lean_Elab_App_10__elabAppArgs___closed__6 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__6);
l___private_Lean_Elab_App_10__elabAppArgs___closed__7 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__7);
l___private_Lean_Elab_App_10__elabAppArgs___closed__8 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__8);
l___private_Lean_Elab_App_10__elabAppArgs___closed__9 = _init_l___private_Lean_Elab_App_10__elabAppArgs___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgs___closed__9);
l___private_Lean_Elab_App_13__resolveLValAux___closed__1 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__1);
l___private_Lean_Elab_App_13__resolveLValAux___closed__2 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__2);
l___private_Lean_Elab_App_13__resolveLValAux___closed__3 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__3);
l___private_Lean_Elab_App_13__resolveLValAux___closed__4 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__4);
l___private_Lean_Elab_App_13__resolveLValAux___closed__5 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__5);
l___private_Lean_Elab_App_13__resolveLValAux___closed__6 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__6);
l___private_Lean_Elab_App_13__resolveLValAux___closed__7 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__7);
l___private_Lean_Elab_App_13__resolveLValAux___closed__8 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__8);
l___private_Lean_Elab_App_13__resolveLValAux___closed__9 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__9);
l___private_Lean_Elab_App_13__resolveLValAux___closed__10 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__10);
l___private_Lean_Elab_App_13__resolveLValAux___closed__11 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__11);
l___private_Lean_Elab_App_13__resolveLValAux___closed__12 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__12);
l___private_Lean_Elab_App_13__resolveLValAux___closed__13 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__13);
l___private_Lean_Elab_App_13__resolveLValAux___closed__14 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__14);
l___private_Lean_Elab_App_13__resolveLValAux___closed__15 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__15);
l___private_Lean_Elab_App_13__resolveLValAux___closed__16 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__16);
l___private_Lean_Elab_App_13__resolveLValAux___closed__17 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__17);
l___private_Lean_Elab_App_13__resolveLValAux___closed__18 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__18);
l___private_Lean_Elab_App_13__resolveLValAux___closed__19 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__19);
l___private_Lean_Elab_App_13__resolveLValAux___closed__20 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__20);
l___private_Lean_Elab_App_13__resolveLValAux___closed__21 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__21);
l___private_Lean_Elab_App_13__resolveLValAux___closed__22 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__22);
l___private_Lean_Elab_App_13__resolveLValAux___closed__23 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__23();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__23);
l___private_Lean_Elab_App_13__resolveLValAux___closed__24 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__24();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__24);
l___private_Lean_Elab_App_13__resolveLValAux___closed__25 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__25();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__25);
l___private_Lean_Elab_App_13__resolveLValAux___closed__26 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__26();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__26);
l___private_Lean_Elab_App_13__resolveLValAux___closed__27 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__27();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__27);
l___private_Lean_Elab_App_13__resolveLValAux___closed__28 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__28();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__28);
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
l___private_Lean_Elab_App_25__toMessageData___closed__1 = _init_l___private_Lean_Elab_App_25__toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_25__toMessageData___closed__1);
l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__2);
l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__3 = _init_l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_27__mergeFailures___rarg___closed__3);
l___private_Lean_Elab_App_28__elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_28__elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_28__elabAppAux___closed__1);
l___private_Lean_Elab_App_28__elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_28__elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_28__elabAppAux___closed__2);
l___private_Lean_Elab_App_28__elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_28__elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_28__elabAppAux___closed__3);
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
res = l___private_Lean_Elab_App_30__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
