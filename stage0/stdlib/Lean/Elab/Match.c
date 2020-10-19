// Lean compiler output
// Module: Lean.Elab.Match
// Imports: Init Lean.Meta.Match.MatchPatternAttr Lean.Meta.Match.Match Lean.Elab.SyntheticMVars Lean.Elab.App
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__2(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__19;
lean_object* l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__25(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__12___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop(lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__15___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22;
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__17(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__4(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
extern lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__14(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__8(lean_object*);
extern lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3;
lean_object* l_Lean_Elab_Term_PatternVar_hasToString_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__5(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1(lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__5(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
lean_object* l_Lean_Elab_Term_elabMatch_match__8___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2___rarg(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed(lean_object**);
extern lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3;
extern lean_object* l_Lean_Parser_registerRunParserAttributeHooksAttribute___lambda__1___closed__1;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__15;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__20(lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___closed__3;
lean_object* l_Lean_Elab_Term_elabMatch_match__7(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_getPatternVars_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__5___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1(lean_object*);
extern lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_object* l_Lean_Elab_Term_mkMatchAltView___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_getNextParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__20___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__11___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
extern lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Term_elabMatch_match__24___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Hygiene_1__mkInaccessibleUserNameAux___closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__13(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__4(lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_State_found___default;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExpr___closed__1;
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__11(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__25___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
lean_object* l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__23(lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__6(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4;
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandMacros___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1;
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1;
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__19(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__9(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalDecl_Inhabited;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1(lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__26(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_State_found___default;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__18___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__10___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId___boxed(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4(lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__15(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_13__quoteName___main___closed__2;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__16(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__10(lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__1(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__22(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__1(lean_object*);
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1(lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_17__mapSepElemsMAux___main___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_State_vars___default;
lean_object* l_Lean_Elab_Term_elabMatch_match__7___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__3___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__26___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1(lean_object*);
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_13__quoteName___main___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__21(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__24(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__22___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__19___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1;
extern lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__9___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* l___private_Init_LeanInit_17__mapSepElemsMAux___main___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_regTraceClasses(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__4(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3;
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars(lean_object*);
lean_object* l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3;
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3(lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__13___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1(lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__12(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__6;
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__17___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
lean_object* l_Lean_Elab_Term_elabMatch_match__16___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__14___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
lean_object* l_Lean_Elab_Term_elabMatch_match__23___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__1;
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__18(lean_object*);
extern lean_object* l_Lean_matchPatternAttr;
lean_object* l_Lean_Elab_Term_getPatternVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Syntax_getSepArgs(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkMatchAltView___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_mkMatchAltView(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_11, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Array_empty___closed__1;
x_18 = lean_array_push(x_17, x_3);
x_19 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_array_push(x_23, x_2);
x_25 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_17, x_26);
x_28 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
x_31 = lean_array_push(x_30, x_29);
x_32 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_array_push(x_33, x_4);
x_35 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_6, 6);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_6, 6, x_40);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTerm(x_36, x_5, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
x_45 = lean_ctor_get(x_6, 2);
x_46 = lean_ctor_get(x_6, 3);
x_47 = lean_ctor_get(x_6, 4);
x_48 = lean_ctor_get(x_6, 5);
x_49 = lean_ctor_get(x_6, 6);
x_50 = lean_ctor_get(x_6, 7);
x_51 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_52 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
lean_inc(x_36);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_36);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set(x_55, 4, x_47);
lean_ctor_set(x_55, 5, x_48);
lean_ctor_set(x_55, 6, x_54);
lean_ctor_set(x_55, 7, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*8, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 1, x_52);
x_56 = 1;
x_57 = l_Lean_Elab_Term_elabTerm(x_36, x_5, x_56, x_55, x_7, x_8, x_9, x_10, x_11, x_16);
return x_57;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_14 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_12, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_empty___closed__1;
x_19 = lean_array_push(x_18, x_3);
x_20 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_21 = lean_array_push(x_19, x_20);
x_22 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
x_23 = lean_array_push(x_22, x_4);
x_24 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_push(x_18, x_25);
x_27 = l_Lean_nullKind___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_21, x_28);
x_30 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_array_push(x_31, x_2);
x_33 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_18, x_34);
x_36 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_array_push(x_41, x_5);
x_43 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_7, 6);
lean_inc(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_7, 6, x_48);
x_49 = 1;
x_50 = l_Lean_Elab_Term_elabTerm(x_44, x_6, x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
x_53 = lean_ctor_get(x_7, 2);
x_54 = lean_ctor_get(x_7, 3);
x_55 = lean_ctor_get(x_7, 4);
x_56 = lean_ctor_get(x_7, 5);
x_57 = lean_ctor_get(x_7, 6);
x_58 = lean_ctor_get(x_7, 7);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
x_60 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 1);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
lean_inc(x_44);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_44);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
x_63 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
lean_ctor_set(x_63, 5, x_56);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_63, 7, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*8, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*8 + 1, x_60);
x_64 = 1;
x_65 = l_Lean_Elab_Term_elabTerm(x_44, x_6, x_64, x_63, x_8, x_9, x_10, x_11, x_12, x_17);
return x_65;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid type provided to match-expression, function type with arity #");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discr #");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_16 = x_11;
} else {
 lean_dec_ref(x_11);
 x_16 = lean_box(0);
}
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_14, x_17);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_12, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Syntax_getArg(x_5, x_17);
lean_inc(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_26 = lean_box(0);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_6, 2);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 1;
lean_ctor_set_uint8(x_27, 0, x_31);
lean_ctor_set_uint8(x_27, 1, x_31);
lean_ctor_set_uint8(x_27, 2, x_31);
lean_ctor_set_uint8(x_27, 3, x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Elab_Term_elabTermEnsuringType(x_24, x_25, x_31, x_26, x_2, x_3, x_32, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_76 = lean_st_ref_get(x_9, x_35);
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
x_37 = x_81;
x_38 = x_80;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_84 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_83, x_2, x_3, x_6, x_7, x_8, x_9, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_37 = x_87;
x_38 = x_86;
goto block_75;
}
block_75:
{
if (x_37 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_expr_instantiate1(x_23, x_34);
lean_dec(x_23);
x_40 = lean_array_push(x_15, x_34);
if (lean_is_scalar(x_16)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_16;
}
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_13)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_13;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_36)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_36;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_36);
lean_inc(x_18);
x_45 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_18);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_34);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_34);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_22);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_60 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_59, x_58, x_2, x_3, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_expr_instantiate1(x_23, x_34);
lean_dec(x_23);
x_64 = lean_array_push(x_15, x_34);
if (lean_is_scalar(x_16)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_16;
}
lean_ctor_set(x_65, 0, x_18);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_13)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_13;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_60, 0, x_67);
return x_60;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_dec(x_60);
x_69 = lean_expr_instantiate1(x_23, x_34);
lean_dec(x_23);
x_70 = lean_array_push(x_15, x_34);
if (lean_is_scalar(x_16)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_16;
}
lean_ctor_set(x_71, 0, x_18);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_13)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_13;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_33);
if (x_88 == 0)
{
return x_33;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_33, 0);
x_90 = lean_ctor_get(x_33, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_33);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get_uint8(x_27, 4);
x_93 = lean_ctor_get_uint8(x_27, 5);
x_94 = lean_ctor_get_uint8(x_27, 6);
x_95 = lean_ctor_get_uint8(x_27, 7);
lean_dec(x_27);
x_96 = 1;
x_97 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_97, 0, x_96);
lean_ctor_set_uint8(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, 2, x_96);
lean_ctor_set_uint8(x_97, 3, x_96);
lean_ctor_set_uint8(x_97, 4, x_92);
lean_ctor_set_uint8(x_97, 5, x_93);
lean_ctor_set_uint8(x_97, 6, x_94);
lean_ctor_set_uint8(x_97, 7, x_95);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_28);
lean_ctor_set(x_98, 2, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_99 = l_Lean_Elab_Term_elabTermEnsuringType(x_24, x_25, x_96, x_26, x_2, x_3, x_98, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
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
x_136 = lean_st_ref_get(x_9, x_101);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 3);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_ctor_get_uint8(x_138, sizeof(void*)*1);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_dec(x_136);
x_141 = 0;
x_103 = x_141;
x_104 = x_140;
goto block_135;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_dec(x_136);
x_143 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_144 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_143, x_2, x_3, x_6, x_7, x_8, x_9, x_142);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_unbox(x_145);
lean_dec(x_145);
x_103 = x_147;
x_104 = x_146;
goto block_135;
}
block_135:
{
if (x_103 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_expr_instantiate1(x_23, x_100);
lean_dec(x_23);
x_106 = lean_array_push(x_15, x_100);
if (lean_is_scalar(x_16)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_16;
}
lean_ctor_set(x_107, 0, x_18);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_13)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_13;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_102;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_102);
lean_inc(x_18);
x_111 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_18);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_100);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_100);
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_121, 0, x_22);
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_126 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_125, x_124, x_2, x_3, x_6, x_7, x_8, x_9, x_104);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
x_129 = lean_expr_instantiate1(x_23, x_100);
lean_dec(x_23);
x_130 = lean_array_push(x_15, x_100);
if (lean_is_scalar(x_16)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_16;
}
lean_ctor_set(x_131, 0, x_18);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_13)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_13;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_127);
return x_134;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_99, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_99, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_150 = x_99;
} else {
 lean_dec_ref(x_99);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_152 = lean_ctor_get(x_19, 1);
lean_inc(x_152);
lean_dec(x_19);
x_153 = lean_array_get_size(x_4);
x_154 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_153);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2;
x_157 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4;
x_159 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_159, x_2, x_3, x_6, x_7, x_8, x_9, x_152);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
return x_160;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_19);
if (x_165 == 0)
{
return x_19;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_19, 0);
x_167 = lean_ctor_get(x_19, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_19);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_7(x_16, lean_box(0), x_14, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(x_3, x_1, x_4, x_5, x_20, x_18, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_5 < x_4;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_7(x_16, lean_box(0), x_6, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_array_uget(x_3, x_5);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
x_20 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed), 10, 5);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_7);
lean_closure_set(x_20, 2, x_8);
lean_closure_set(x_20, 3, x_1);
lean_closure_set(x_20, 4, x_18);
x_21 = lean_box_usize(x_5);
x_22 = lean_box_usize(x_4);
x_23 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed), 13, 7);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_22);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_8);
x_24 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_20, x_23, x_9, x_10, x_11, x_12, x_13);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_1);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
lean_inc(x_1);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(x_1, x_16, x_1, x_14, x_15, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_LocalDecl_userName(x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_LocalDecl_userName(x_14);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
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
lean_dec(x_1);
x_22 = l_Lean_Elab_Term_mkFreshBinderName(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_discr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_erase_macro_scopes(x_1);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_3(x_2, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected discriminant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_isLocalIdent_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3;
x_15 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_6);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_LocalDecl_userName(x_21);
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_22);
if (x_23 == 0)
{
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_24; 
lean_dec(x_16);
x_24 = l_Lean_LocalDecl_value(x_21);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = l_Lean_LocalDecl_userName(x_25);
x_28 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
x_30 = l_Lean_LocalDecl_value(x_25);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_16);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_32; 
x_32 = l_Lean_Expr_isFVar(x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_11 = x_33;
goto block_31;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Occurrences_beq(x_3, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_11 = x_36;
goto block_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_2);
x_39 = lean_expr_abstract(x_1, x_38);
lean_dec(x_38);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_12 = l_Lean_Expr_toHeadIndex___main(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_st_mk_ref(x_15, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_12, x_14, x_1, x_13, x_17, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_17, x_21);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc(x_2);
x_16 = l_Array_insertAt___rarg(x_13, x_15, x_2);
lean_dec(x_15);
lean_ctor_set(x_11, 1, x_16);
x_17 = lean_nat_add(x_3, x_14);
x_18 = x_11;
x_19 = lean_array_fset(x_10, x_3, x_18);
lean_dec(x_3);
x_3 = x_17;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
lean_inc(x_2);
x_26 = l_Array_insertAt___rarg(x_22, x_25, x_2);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
x_28 = lean_nat_add(x_3, x_24);
x_29 = x_27;
x_30 = lean_array_fset(x_10, x_3, x_29);
lean_dec(x_3);
x_3 = x_28;
x_4 = x_30;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_expr_instantiate1(x_1, x_2);
x_18 = l_Lean_mkAppStx___closed__9;
x_19 = lean_array_push(x_18, x_2);
x_20 = lean_array_push(x_19, x_9);
lean_inc(x_12);
x_21 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_20, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_3);
x_24 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_3, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_push(x_4, x_25);
x_28 = lean_array_push(x_27, x_3);
x_29 = x_5;
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(x_6, x_7, x_30, x_29);
x_32 = x_31;
x_33 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(x_8, x_6, x_28, x_22, x_32, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_1, x_8, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Syntax_getId(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed), 16, 8);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_8);
lean_closure_set(x_20, 2, x_1);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_2);
lean_closure_set(x_20, 7, x_7);
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_19, x_21, x_17, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_Syntax_inhabited;
x_18 = lean_array_get(x_17, x_1, x_16);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_23);
x_25 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_23);
x_32 = l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(x_4, x_23, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_23);
x_35 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Syntax_getArg(x_18, x_13);
lean_dec(x_18);
x_39 = l_Lean_Syntax_isNone(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_40 = l_Lean_Syntax_getArg(x_38, x_13);
lean_dec(x_38);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2), 15, 7);
lean_closure_set(x_41, 0, x_23);
lean_closure_set(x_41, 1, x_40);
lean_closure_set(x_41, 2, x_33);
lean_closure_set(x_41, 3, x_3);
lean_closure_set(x_41, 4, x_5);
lean_closure_set(x_41, 5, x_16);
lean_closure_set(x_41, 6, x_1);
x_42 = 0;
x_43 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_36, x_42, x_29, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_38);
x_44 = lean_array_push(x_3, x_23);
x_45 = 0;
x_46 = l_Lean_mkForall(x_36, x_45, x_29, x_33);
x_2 = x_16;
x_3 = x_44;
x_4 = x_46;
x_12 = x_37;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_19);
if (x_60 == 0)
{
return x_19;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_19, 0);
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_19);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_64 = l_Array_reverseAux___main___rarg(x_3, x_13);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_5);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_12);
return x_67;
}
}
}
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Syntax_isNone(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_elabType(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_array_get_size(x_1);
x_39 = l_Array_empty___closed__1;
x_40 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(x_1, x_38, x_39, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_40;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_3);
x_13 = l_Lean_expandMacros___main(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean_array_fset(x_11, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_3);
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
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = x_15;
x_18 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 4, 2);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_17);
x_19 = x_18;
lean_inc(x_3);
x_20 = lean_apply_2(x_19, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_12, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_1, x_23);
x_25 = x_12;
x_26 = lean_array_fset(x_11, x_1, x_25);
lean_dec(x_1);
x_1 = x_24;
x_2 = x_26;
x_4 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
x_34 = lean_ctor_get(x_12, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_35 = x_33;
x_36 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 4, 2);
lean_closure_set(x_36, 0, x_10);
lean_closure_set(x_36, 1, x_35);
x_37 = x_36;
lean_inc(x_3);
x_38 = lean_apply_2(x_37, x_3, x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_34);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_1, x_42);
x_44 = x_41;
x_45 = lean_array_fset(x_11, x_1, x_44);
lean_dec(x_1);
x_1 = x_43;
x_2 = x_45;
x_4 = x_40;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = x_1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = x_6;
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
x_7 = lean_name_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_10 = l_Lean_Elab_Term_mkMatchAltView(x_2, x_1);
lean_dec(x_1);
x_11 = lean_array_push(x_3, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Syntax_isNone(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_box(0);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1(x_6, x_7, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_7);
x_16 = lean_box(0);
lean_inc(x_6);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1(x_6, x_6, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = x_3 + x_19;
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = l_Array_empty___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_get_size(x_8);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(x_8, x_12, x_13, x_10);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Hygiene_1__mkInaccessibleUserNameAux___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Hygiene_1__mkInaccessibleUserNameAux___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_inaccessible_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_PatternVar_hasToString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_PatternVar_hasToString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_PatternVar_hasToString_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_PatternVar_hasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?m");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_PatternVar_hasToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_String_splitAux___main___closed__1;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MVarWithIdKind");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2;
x_3 = l_Lean_Parser_registerBuiltinNodeKind(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___spec__1___rarg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_mkOptionalNode___closed__2;
x_9 = lean_array_push(x_8, x_7);
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_mkOptionalNode___closed__2;
x_17 = lean_array_push(x_16, x_15);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getKind(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_1);
x_11 = l_Lean_mkMVar(x_10);
x_12 = l_Lean_Elab_Term_mkInaccessible(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabMVarWithIdKind(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMVarWithIdKind___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = 1;
x_13 = l_Lean_Elab_Term_elabTerm(x_11, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Elab_Term_mkInaccessible(x_15);
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
x_19 = l_Lean_Elab_Term_mkInaccessible(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
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
}
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabInaccessible(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inaccessible");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabInaccessible___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_found___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, constructor or constant marked with '[matchPattern]' expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
lean_dec(x_14);
lean_inc(x_7);
x_16 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_binderInfo(x_17);
lean_dec(x_17);
x_20 = l_Lean_BinderInfo_isExplicit(x_19);
if (x_20 == 0)
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_3 + x_21;
x_3 = x_22;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = 1;
x_27 = x_3 + x_26;
x_3 = x_27;
x_4 = x_25;
x_11 = x_18;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(x_1, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1(x_1, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1;
x_14 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg(x_10, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous pattern, use fully qualified name, possible interpretations ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_1);
x_11 = l_Lean_MessageData_ofList(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_apply_1(x_4, x_1);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_List_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_List_isEmpty___rarg(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(lean_object* x_1) {
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
x_6 = l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_7);
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
x_10 = l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_9);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(x_1, x_10);
x_12 = l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1;
x_13 = lean_box(0);
lean_inc(x_5);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_resolveName(x_10, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_9(x_12, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_apply_9(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_21 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_2);
lean_ctor_set(x_7, 6, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*7 + 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1;
return x_1;
}
}
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_array_get_size(x_2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_nat_dec_le(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
x_36 = l_Array_isEmpty___rarg(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 0;
x_10 = x_37;
goto block_34;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 5);
lean_inc(x_38);
x_39 = l_List_isEmpty___rarg(x_38);
lean_dec(x_38);
x_10 = x_39;
goto block_34;
}
block_34:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3;
x_12 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_20 = lean_array_push(x_19, x_18);
x_21 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_ctor_get(x_1, 6);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_mkAppStx(x_22, x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_28 = lean_array_push(x_27, x_26);
x_29 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_ctor_get(x_1, 6);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_mkAppStx(x_30, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = l_Lean_LocalDecl_binderInfo(x_8);
lean_dec(x_8);
x_10 = l_Lean_BinderInfo_isExplicit(x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_12, 3);
x_14 = lean_nat_dec_le(x_13, x_11);
return x_14;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_getNextParam(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_LocalDecl_Inhabited;
x_6 = lean_array_get(x_5, x_3, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get(x_1, 5);
x_18 = lean_ctor_get(x_1, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_19 = l_Lean_LocalDecl_Inhabited;
x_20 = lean_array_get(x_19, x_14, x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_15, x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 1, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_array_push(x_12, x_2);
lean_ctor_set(x_1, 6, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get(x_1, 4);
x_22 = lean_ctor_get(x_1, 5);
x_23 = lean_ctor_get(x_1, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_24 = lean_array_push(x_23, x_2);
x_25 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_2 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Match");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.Match.0.Lean.Elab.Term.CollectPatternVars.CtorApp.pushNewArg");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3;
x_3 = lean_unsigned_to_nat(307u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (x_2 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = lean_apply_9(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1;
x_25 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4;
x_26 = lean_panic_fn(x_24, x_25);
x_27 = lean_apply_8(x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_map___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(x_5);
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
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter is missing, unused named arguments ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 5);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_dec(x_3);
x_15 = x_14;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(x_16, x_15);
x_18 = x_17;
x_19 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_20 = l_List_map___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(x_19);
x_21 = l_Lean_MessageData_ofList(x_20);
lean_dec(x_20);
x_22 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3;
x_32 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_3, 5);
lean_dec(x_34);
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
lean_ctor_set(x_3, 5, x_36);
x_37 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_42 = lean_ctor_get(x_3, 2);
x_43 = lean_ctor_get(x_3, 3);
x_44 = lean_ctor_get(x_3, 4);
x_45 = lean_ctor_get(x_3, 6);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_44);
lean_ctor_set(x_48, 5, x_47);
lean_ctor_set(x_48, 6, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*7, x_40);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 1, x_41);
x_49 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_48, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_49;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3;
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible(x_2);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_getNextParam(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 1);
x_20 = lean_ctor_get(x_14, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 6);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux___spec__1(x_15, x_22, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_27 = l_Lean_LocalDecl_binderInfo(x_15);
lean_dec(x_15);
x_28 = lean_box(x_27);
switch (lean_obj_tag(x_28)) {
case 1:
{
lean_object* x_29; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_29 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_2 = x_30;
x_10 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
case 3:
{
lean_object* x_37; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_37 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_2 = x_38;
x_10 = x_39;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
default: 
{
lean_object* x_45; 
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_45 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_2 = x_46;
x_10 = x_47;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_15);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_14, 6);
lean_dec(x_54);
x_55 = lean_ctor_get(x_14, 5);
lean_dec(x_55);
x_56 = lean_ctor_get(x_14, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_14, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_14, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_14, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_14, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_26, 0);
lean_inc(x_61);
lean_dec(x_26);
x_62 = l_Lean_Elab_Term_NamedArg_inhabited;
x_63 = lean_array_get(x_62, x_22, x_61);
x_64 = l_Array_eraseIdx___rarg(x_22, x_61);
lean_dec(x_61);
lean_ctor_set(x_14, 4, x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_66 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_12, x_14, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_2 = x_67;
x_10 = x_68;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_14);
x_74 = lean_ctor_get(x_26, 0);
lean_inc(x_74);
lean_dec(x_26);
x_75 = l_Lean_Elab_Term_NamedArg_inhabited;
x_76 = lean_array_get(x_75, x_22, x_74);
x_77 = l_Array_eraseIdx___rarg(x_22, x_74);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_78, 0, x_16);
lean_ctor_set(x_78, 1, x_17);
lean_ctor_set(x_78, 2, x_20);
lean_ctor_set(x_78, 3, x_21);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 5, x_23);
lean_ctor_set(x_78, 6, x_24);
lean_ctor_set_uint8(x_78, sizeof(void*)*7, x_18);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 1, x_19);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_80 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_12, x_78, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_2 = x_81;
x_10 = x_82;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_86 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
}
else
{
lean_object* x_88; 
lean_dec(x_1);
x_88 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_88;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_3(x_2, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = lean_environment_find(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_10);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = lean_environment_find(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_1);
x_28 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_fvarId_x21(x_1);
x_11 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
lean_inc(x_6);
x_19 = l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = x_9;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed), 10, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
x_22 = x_21;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_23 = lean_apply_8(x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_20);
lean_ctor_set(x_29, 4, x_6);
lean_ctor_set(x_29, 5, x_7);
lean_ctor_set(x_29, 6, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 1, x_5);
x_30 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(x_8, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_st_ref_get(x_17, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_matchPatternAttr;
x_38 = l_Lean_TagAttribute_hasTag(x_37, x_36, x_2);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_39 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = l_Array_empty___closed__1;
x_42 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_20);
lean_ctor_set(x_42, 4, x_6);
lean_ctor_set(x_42, 5, x_7);
lean_ctor_set(x_42, 6, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 1, x_5);
x_43 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(x_8, x_42, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_35);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_44; lean_object* x_52; uint8_t x_53; 
x_14 = l_Array_toList___rarg(x_4);
x_52 = l_Lean_identKind___closed__2;
lean_inc(x_2);
x_53 = l_Lean_Syntax_isOfKind(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_inc(x_2);
x_55 = l_Lean_Syntax_isOfKind(x_2, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_44 = x_56;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l_Lean_Syntax_getArgs(x_2);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_44 = x_61;
goto block_51;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Syntax_getArg(x_2, x_62);
lean_dec(x_2);
lean_inc(x_63);
x_64 = l_Lean_Syntax_isOfKind(x_63, x_52);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_63);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_65 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_66 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
x_15 = x_73;
x_16 = x_13;
goto block_43;
}
}
}
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_75);
x_15 = x_76;
x_16 = x_13;
goto block_43;
}
block_43:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
x_19 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_25);
x_26 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ConstantInfo_type(x_27);
x_30 = lean_box(x_5);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed), 18, 8);
lean_closure_set(x_31, 0, x_27);
lean_closure_set(x_31, 1, x_25);
lean_closure_set(x_31, 2, x_17);
lean_closure_set(x_31, 3, x_18);
lean_closure_set(x_31, 4, x_30);
lean_closure_set(x_31, 5, x_3);
lean_closure_set(x_31, 6, x_14);
lean_closure_set(x_31, 7, x_1);
x_32 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(x_29, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
block_51:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_44);
x_45 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_46 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_45, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(x_1, x_2, x_3, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_inc(x_8);
lean_inc(x_4);
x_12 = l_Lean_Elab_Term_expandApp(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(x_1, x_17, x_18, x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Array_empty___closed__1;
x_12 = 0;
x_13 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(x_1, x_2, x_11, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_12);
lean_dec(x_13);
lean_ctor_set(x_8, 3, x_14);
x_15 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_8, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_20 = l_Lean_replaceRef(x_1, x_19);
x_21 = l_Lean_replaceRef(x_20, x_19);
lean_dec(x_19);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_21);
x_23 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_10);
lean_dec(x_22);
return x_23;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_15, x_1, x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_st_ref_set(x_4, x_21, x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, variable '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurred more than once");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_NameSet_contains(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
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
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern variable, must be atomic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Syntax_getId(x_1);
lean_inc(x_11);
x_12 = lean_erase_macro_scopes(x_11);
x_13 = l_Lean_Name_isAtomic(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(x_11, x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Syntax_isIdent(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
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
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_18;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_7);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_21);
lean_inc(x_14);
x_22 = lean_environment_find(x_14, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 6)
{
lean_object* x_25; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
x_25 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = l_Lean_matchPatternAttr;
x_27 = l_Lean_TagAttribute_hasTag(x_26, x_14, x_21);
lean_dec(x_21);
lean_dec(x_14);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.anonymous");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Init_LeanInit_13__quoteName___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_2 = l___private_Init_LeanInit_13__quoteName___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExpr___closed__1;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExpr___closed__1;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Parser_registerRunParserAttributeHooksAttribute___lambda__1___closed__1;
x_16 = l_Lean_addMacroScope(x_14, x_15, x_10);
x_17 = l_Lean_SourceInfo_inhabited___closed__1;
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = l_Lean_Parser_registerRunParserAttributeHooksAttribute___lambda__1___closed__1;
x_24 = l_Lean_addMacroScope(x_21, x_23, x_10);
x_25 = l_Lean_SourceInfo_inhabited___closed__1;
x_26 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
x_42 = l_Lean_addMacroScope(x_40, x_41, x_36);
x_43 = l_Lean_SourceInfo_inhabited___closed__1;
x_44 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_45 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Array_empty___closed__1;
x_48 = lean_array_push(x_47, x_46);
x_49 = lean_array_push(x_47, x_33);
x_50 = l_Lean_mkStxStrLit(x_31, x_43);
lean_dec(x_31);
x_51 = lean_array_push(x_49, x_50);
x_52 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_53 = lean_array_push(x_51, x_52);
x_54 = l_Lean_nullKind___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_48, x_55);
x_57 = l_Lean_mkAppStx___closed__8;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_38, 0, x_58);
return x_38;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_38);
x_61 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
x_62 = l_Lean_addMacroScope(x_59, x_61, x_36);
x_63 = l_Lean_SourceInfo_inhabited___closed__1;
x_64 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_65 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_65);
x_67 = l_Array_empty___closed__1;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_array_push(x_67, x_33);
x_70 = l_Lean_mkStxStrLit(x_31, x_63);
lean_dec(x_31);
x_71 = lean_array_push(x_69, x_70);
x_72 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_73 = lean_array_push(x_71, x_72);
x_74 = l_Lean_nullKind___closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_array_push(x_68, x_75);
x_77 = l_Lean_mkAppStx___closed__8;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_60);
return x_79;
}
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_82 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_87);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
x_92 = l_Lean_addMacroScope(x_90, x_91, x_86);
x_93 = l_Lean_SourceInfo_inhabited___closed__1;
x_94 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_95 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_92);
lean_ctor_set(x_96, 3, x_95);
x_97 = l_Array_empty___closed__1;
x_98 = lean_array_push(x_97, x_96);
x_99 = lean_array_push(x_97, x_83);
x_100 = l_Nat_repr(x_81);
x_101 = l_Lean_numLitKind;
x_102 = l_Lean_mkStxLit(x_101, x_100, x_93);
x_103 = lean_array_push(x_99, x_102);
x_104 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_105 = lean_array_push(x_103, x_104);
x_106 = l_Lean_nullKind___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_98, x_107);
x_109 = l_Lean_mkAppStx___closed__8;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_88, 0, x_110);
return x_88;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_111 = lean_ctor_get(x_88, 0);
x_112 = lean_ctor_get(x_88, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_88);
x_113 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
x_114 = l_Lean_addMacroScope(x_111, x_113, x_86);
x_115 = l_Lean_SourceInfo_inhabited___closed__1;
x_116 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_117 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_118 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_118, 2, x_114);
lean_ctor_set(x_118, 3, x_117);
x_119 = l_Array_empty___closed__1;
x_120 = lean_array_push(x_119, x_118);
x_121 = lean_array_push(x_119, x_83);
x_122 = l_Nat_repr(x_81);
x_123 = l_Lean_numLitKind;
x_124 = l_Lean_mkStxLit(x_123, x_122, x_115);
x_125 = lean_array_push(x_121, x_124);
x_126 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_127 = lean_array_push(x_125, x_126);
x_128 = l_Lean_nullKind___closed__2;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_array_push(x_120, x_129);
x_131 = l_Lean_mkAppStx___closed__8;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_112);
return x_133;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNameLit_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_14;
}
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_apply_3(x_2, x_1, x_5, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_apply_5(x_3, x_1, x_8, x_9, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_17__mapSepElemsMAux___main___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_fget(x_1, x_3);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_mod(x_3, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_23 = lean_array_push(x_4, x_16);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = lean_apply_9(x_2, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_30 = lean_array_push(x_4, x_26);
x_3 = x_29;
x_4 = x_30;
x_12 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
}
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Init_LeanInit_17__mapSepElemsMAux___main___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Syntax_setArg(x_1, x_10, x_14);
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
x_18 = l_Lean_Syntax_setArg(x_1, x_10, x_16);
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
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Syntax_inhabited;
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_12, x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1;
x_17 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_nullKind;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_set(x_1, x_13, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Lean_nullKind;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_array_set(x_1, x_13, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymousCtor");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, notation is ambiguous");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid struct instance pattern, 'with' is not allowed in patterns");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Lean_mkAppStx___closed__8;
x_13 = lean_name_eq(x_10, x_12);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_7, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
lean_ctor_set(x_7, 3, x_17);
x_18 = lean_st_ref_take(x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_ctor_set(x_19, 1, x_24);
x_25 = lean_st_ref_set(x_8, x_19, x_20);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_3, 7);
lean_dec(x_30);
lean_ctor_set(x_3, 7, x_22);
if (x_13 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_32 = lean_name_eq(x_10, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_34 = lean_name_eq(x_10, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_mkHole___closed__2;
x_36 = lean_name_eq(x_10, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_38 = lean_name_eq(x_10, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_11);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
x_40 = lean_name_eq(x_10, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
x_42 = lean_name_eq(x_10, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_44 = lean_name_eq(x_10, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_strLitKind;
x_46 = lean_name_eq(x_10, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_numLitKind;
x_48 = lean_name_eq(x_10, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_charLitKind;
x_50 = lean_name_eq(x_10, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
lean_free_object(x_25);
x_51 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_52 = lean_name_eq(x_10, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_1);
x_53 = l_Lean_choiceKind;
x_54 = lean_name_eq(x_10, x_53);
lean_dec(x_10);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_57 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_10);
lean_dec(x_2);
x_58 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_58;
}
}
else
{
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_25);
lean_dec(x_10);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
lean_inc(x_7);
lean_inc(x_60);
x_61 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = l_Lean_Syntax_getArg(x_1, x_63);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_1, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 0);
lean_dec(x_67);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_Lean_Elab_Term_CollectPatternVars_collect(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_70);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_73);
lean_dec(x_8);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_78 = l_Lean_addMacroScope(x_76, x_77, x_72);
x_79 = l_Lean_SourceInfo_inhabited___closed__1;
x_80 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_81 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Array_empty___closed__1;
x_84 = lean_array_push(x_83, x_82);
x_85 = lean_array_push(x_83, x_60);
x_86 = lean_array_push(x_85, x_69);
x_87 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_86);
lean_ctor_set(x_1, 0, x_87);
x_88 = lean_array_push(x_84, x_1);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_12);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_74, 0, x_89);
return x_74;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_ctor_get(x_74, 0);
x_91 = lean_ctor_get(x_74, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_74);
x_92 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_93 = l_Lean_addMacroScope(x_90, x_92, x_72);
x_94 = l_Lean_SourceInfo_inhabited___closed__1;
x_95 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_96 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_96);
x_98 = l_Array_empty___closed__1;
x_99 = lean_array_push(x_98, x_97);
x_100 = lean_array_push(x_98, x_60);
x_101 = lean_array_push(x_100, x_69);
x_102 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_101);
lean_ctor_set(x_1, 0, x_102);
x_103 = lean_array_push(x_99, x_1);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_12);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_91);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_free_object(x_1);
lean_dec(x_60);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = !lean_is_exclusive(x_68);
if (x_106 == 0)
{
return x_68;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_68, 0);
x_108 = lean_ctor_get(x_68, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_68);
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
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_110 = l_Lean_Elab_Term_CollectPatternVars_collect(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_112);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_115);
lean_dec(x_8);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_121 = l_Lean_addMacroScope(x_117, x_120, x_114);
x_122 = l_Lean_SourceInfo_inhabited___closed__1;
x_123 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_124 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_125 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_121);
lean_ctor_set(x_125, 3, x_124);
x_126 = l_Array_empty___closed__1;
x_127 = lean_array_push(x_126, x_125);
x_128 = lean_array_push(x_126, x_60);
x_129 = lean_array_push(x_128, x_111);
x_130 = l_Lean_nullKind___closed__2;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_127, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_12);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_119)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_119;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_118);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_60);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_135 = lean_ctor_get(x_110, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_110, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_137 = x_110;
} else {
 lean_dec_ref(x_110);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_60);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_61);
if (x_139 == 0)
{
return x_61;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_61, 0);
x_141 = lean_ctor_get(x_61, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_61);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_25);
lean_dec(x_10);
x_143 = lean_unsigned_to_nat(0u);
x_144 = l_Lean_Syntax_getArg(x_1, x_143);
lean_dec(x_1);
x_145 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_146 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_145, x_144, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_inhabited;
x_148 = lean_array_get(x_147, x_11, x_23);
x_149 = l_Lean_Syntax_isNone(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_208; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_150 = x_1;
} else {
 lean_dec_ref(x_1);
 x_150 = lean_box(0);
}
x_151 = lean_unsigned_to_nat(0u);
x_152 = l_Lean_Syntax_getArg(x_148, x_151);
x_153 = l_Lean_Syntax_getArg(x_148, x_23);
x_208 = l_Lean_Syntax_isNone(x_153);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = l_Lean_Syntax_getArg(x_153, x_151);
x_210 = l_Lean_Syntax_getKind(x_209);
x_211 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_212 = lean_name_eq(x_210, x_211);
lean_dec(x_210);
x_154 = x_212;
goto block_207;
}
else
{
uint8_t x_213; 
x_213 = 1;
x_154 = x_213;
goto block_207;
}
block_207:
{
if (x_154 == 0)
{
lean_object* x_155; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_155 = l_Lean_Elab_Term_CollectPatternVars_collect(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Syntax_setArg(x_148, x_151, x_156);
x_159 = l_Lean_Syntax_getArg(x_153, x_151);
x_160 = l_Lean_Syntax_getArg(x_159, x_23);
x_161 = l_Lean_Syntax_getArgs(x_160);
lean_dec(x_160);
x_162 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_163 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_161, x_162, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_157);
lean_dec(x_161);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = l_Lean_nullKind;
if (lean_is_scalar(x_150)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_150;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_Lean_Syntax_setArg(x_159, x_23, x_167);
x_169 = l_Lean_Syntax_setArg(x_153, x_151, x_168);
x_170 = l_Lean_Syntax_setArg(x_158, x_23, x_169);
x_171 = lean_array_set(x_11, x_23, x_170);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_10);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_163, 0, x_172);
return x_163;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_173 = lean_ctor_get(x_163, 0);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_163);
x_175 = l_Lean_nullKind;
if (lean_is_scalar(x_150)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_150;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
x_177 = l_Lean_Syntax_setArg(x_159, x_23, x_176);
x_178 = l_Lean_Syntax_setArg(x_153, x_151, x_177);
x_179 = l_Lean_Syntax_setArg(x_158, x_23, x_178);
x_180 = lean_array_set(x_11, x_23, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_10);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_174);
return x_182;
}
}
else
{
uint8_t x_183; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_183 = !lean_is_exclusive(x_163);
if (x_183 == 0)
{
return x_163;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_163, 0);
x_185 = lean_ctor_get(x_163, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_163);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_155);
if (x_187 == 0)
{
return x_155;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_155, 0);
x_189 = lean_ctor_get(x_155, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_155);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
lean_object* x_191; 
lean_dec(x_153);
x_191 = l_Lean_Elab_Term_CollectPatternVars_collect(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = l_Lean_Syntax_setArg(x_148, x_151, x_193);
x_195 = lean_array_set(x_11, x_23, x_194);
if (lean_is_scalar(x_150)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_150;
}
lean_ctor_set(x_196, 0, x_10);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_191, 0, x_196);
return x_191;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_197 = lean_ctor_get(x_191, 0);
x_198 = lean_ctor_get(x_191, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_191);
x_199 = l_Lean_Syntax_setArg(x_148, x_151, x_197);
x_200 = lean_array_set(x_11, x_23, x_199);
if (lean_is_scalar(x_150)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_150;
}
lean_ctor_set(x_201, 0, x_10);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_198);
return x_202;
}
}
else
{
uint8_t x_203; 
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_11);
lean_dec(x_10);
x_203 = !lean_is_exclusive(x_191);
if (x_203 == 0)
{
return x_191;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_191, 0);
x_205 = lean_ctor_get(x_191, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_191);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
}
else
{
lean_dec(x_148);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_3);
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_214 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_27);
lean_dec(x_8);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_st_ref_take(x_2, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_221 = lean_ctor_get(x_218, 1);
x_222 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_215);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_224 = lean_array_push(x_221, x_223);
lean_ctor_set(x_218, 1, x_224);
x_225 = lean_st_ref_set(x_2, x_218, x_219);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_225, 0);
lean_dec(x_227);
lean_ctor_set(x_225, 0, x_215);
return x_225;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_215);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_230 = lean_ctor_get(x_218, 0);
x_231 = lean_ctor_get(x_218, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_218);
x_232 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_215);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = lean_array_push(x_231, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_230);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_st_ref_set(x_2, x_235, x_219);
lean_dec(x_2);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_215);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
lean_free_object(x_25);
lean_dec(x_1);
x_240 = l_Lean_Syntax_inhabited;
x_241 = lean_array_get(x_240, x_11, x_23);
x_242 = l_Lean_Syntax_isNone(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
lean_dec(x_11);
lean_dec(x_10);
x_243 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_244 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_241, x_243, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_241);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
return x_244;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_244);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_241);
x_249 = lean_box(0);
x_250 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_11, x_10, x_249, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_free_object(x_25);
x_251 = !lean_is_exclusive(x_1);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_252 = lean_ctor_get(x_1, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_1, 0);
lean_dec(x_253);
x_254 = l_Lean_Syntax_inhabited;
x_255 = lean_array_get(x_254, x_11, x_23);
x_256 = l_Lean_Syntax_getArgs(x_255);
lean_dec(x_255);
x_257 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_258 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_256, x_257, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_256);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_261);
x_262 = lean_array_set(x_11, x_23, x_1);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_10);
lean_ctor_set(x_263, 1, x_262);
lean_ctor_set(x_258, 0, x_263);
return x_258;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_ctor_get(x_258, 0);
x_265 = lean_ctor_get(x_258, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_258);
x_266 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_264);
lean_ctor_set(x_1, 0, x_266);
x_267 = lean_array_set(x_11, x_23, x_1);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_10);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_265);
return x_269;
}
}
else
{
uint8_t x_270; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_270 = !lean_is_exclusive(x_258);
if (x_270 == 0)
{
return x_258;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_258, 0);
x_272 = lean_ctor_get(x_258, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_258);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_1);
x_274 = l_Lean_Syntax_inhabited;
x_275 = lean_array_get(x_274, x_11, x_23);
x_276 = l_Lean_Syntax_getArgs(x_275);
lean_dec(x_275);
x_277 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_278 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_276, x_277, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_276);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_281 = x_278;
} else {
 lean_dec_ref(x_278);
 x_281 = lean_box(0);
}
x_282 = l_Lean_nullKind;
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_279);
x_284 = lean_array_set(x_11, x_23, x_283);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_10);
lean_ctor_set(x_285, 1, x_284);
if (lean_is_scalar(x_281)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_281;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_280);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_11);
lean_dec(x_10);
x_287 = lean_ctor_get(x_278, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_278, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_289 = x_278;
} else {
 lean_dec_ref(x_278);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_291 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_292 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_291, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_1);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; uint8_t x_301; lean_object* x_302; 
x_293 = lean_ctor_get(x_3, 0);
x_294 = lean_ctor_get(x_3, 1);
x_295 = lean_ctor_get(x_3, 2);
x_296 = lean_ctor_get(x_3, 3);
x_297 = lean_ctor_get(x_3, 4);
x_298 = lean_ctor_get(x_3, 5);
x_299 = lean_ctor_get(x_3, 6);
x_300 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_301 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_3);
x_302 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_294);
lean_ctor_set(x_302, 2, x_295);
lean_ctor_set(x_302, 3, x_296);
lean_ctor_set(x_302, 4, x_297);
lean_ctor_set(x_302, 5, x_298);
lean_ctor_set(x_302, 6, x_299);
lean_ctor_set(x_302, 7, x_22);
lean_ctor_set_uint8(x_302, sizeof(void*)*8, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*8 + 1, x_301);
if (x_13 == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_304 = lean_name_eq(x_10, x_303);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_306 = lean_name_eq(x_10, x_305);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; 
x_307 = l_Lean_mkHole___closed__2;
x_308 = lean_name_eq(x_10, x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_310 = lean_name_eq(x_10, x_309);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
lean_dec(x_11);
x_311 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
x_312 = lean_name_eq(x_10, x_311);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
x_314 = lean_name_eq(x_10, x_313);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_316 = lean_name_eq(x_10, x_315);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = l_Lean_strLitKind;
x_318 = lean_name_eq(x_10, x_317);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = l_Lean_numLitKind;
x_320 = lean_name_eq(x_10, x_319);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = l_Lean_charLitKind;
x_322 = lean_name_eq(x_10, x_321);
if (x_322 == 0)
{
lean_object* x_323; uint8_t x_324; 
lean_free_object(x_25);
x_323 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_324 = lean_name_eq(x_10, x_323);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; 
lean_dec(x_1);
x_325 = l_Lean_choiceKind;
x_326 = lean_name_eq(x_10, x_325);
lean_dec(x_10);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_302);
lean_dec(x_2);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_329 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_328, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_302);
lean_dec(x_2);
return x_329;
}
}
else
{
lean_object* x_330; 
lean_dec(x_10);
lean_dec(x_2);
x_330 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_330;
}
}
else
{
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_free_object(x_25);
lean_dec(x_10);
x_331 = lean_unsigned_to_nat(0u);
x_332 = l_Lean_Syntax_getArg(x_1, x_331);
lean_inc(x_7);
lean_inc(x_332);
x_333 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_332, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_335 = lean_unsigned_to_nat(2u);
x_336 = l_Lean_Syntax_getArg(x_1, x_335);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_337 = x_1;
} else {
 lean_dec_ref(x_1);
 x_337 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_302);
x_338 = l_Lean_Elab_Term_CollectPatternVars_collect(x_336, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_334);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_Elab_Term_getCurrMacroScope(x_302, x_4, x_5, x_6, x_7, x_8, x_340);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_302);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_343);
lean_dec(x_8);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
x_348 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_349 = l_Lean_addMacroScope(x_345, x_348, x_342);
x_350 = l_Lean_SourceInfo_inhabited___closed__1;
x_351 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_352 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_353 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
lean_ctor_set(x_353, 2, x_349);
lean_ctor_set(x_353, 3, x_352);
x_354 = l_Array_empty___closed__1;
x_355 = lean_array_push(x_354, x_353);
x_356 = lean_array_push(x_354, x_332);
x_357 = lean_array_push(x_356, x_339);
x_358 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_337)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_337;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = lean_array_push(x_355, x_359);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_12);
lean_ctor_set(x_361, 1, x_360);
if (lean_is_scalar(x_347)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_347;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_346);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_337);
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_363 = lean_ctor_get(x_338, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_338, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_365 = x_338;
} else {
 lean_dec_ref(x_338);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_333, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_333, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_369 = x_333;
} else {
 lean_dec_ref(x_333);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_free_object(x_25);
lean_dec(x_10);
x_371 = lean_unsigned_to_nat(0u);
x_372 = l_Lean_Syntax_getArg(x_1, x_371);
lean_dec(x_1);
x_373 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_374 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_373, x_372, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
return x_374;
}
}
else
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = l_Lean_Syntax_inhabited;
x_376 = lean_array_get(x_375, x_11, x_23);
x_377 = l_Lean_Syntax_isNone(x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_424; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_378 = x_1;
} else {
 lean_dec_ref(x_1);
 x_378 = lean_box(0);
}
x_379 = lean_unsigned_to_nat(0u);
x_380 = l_Lean_Syntax_getArg(x_376, x_379);
x_381 = l_Lean_Syntax_getArg(x_376, x_23);
x_424 = l_Lean_Syntax_isNone(x_381);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_425 = l_Lean_Syntax_getArg(x_381, x_379);
x_426 = l_Lean_Syntax_getKind(x_425);
x_427 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_428 = lean_name_eq(x_426, x_427);
lean_dec(x_426);
x_382 = x_428;
goto block_423;
}
else
{
uint8_t x_429; 
x_429 = 1;
x_382 = x_429;
goto block_423;
}
block_423:
{
if (x_382 == 0)
{
lean_object* x_383; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_302);
lean_inc(x_2);
x_383 = l_Lean_Elab_Term_CollectPatternVars_collect(x_380, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l_Lean_Syntax_setArg(x_376, x_379, x_384);
x_387 = l_Lean_Syntax_getArg(x_381, x_379);
x_388 = l_Lean_Syntax_getArg(x_387, x_23);
x_389 = l_Lean_Syntax_getArgs(x_388);
lean_dec(x_388);
x_390 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_391 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_389, x_390, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_385);
lean_dec(x_389);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_394 = x_391;
} else {
 lean_dec_ref(x_391);
 x_394 = lean_box(0);
}
x_395 = l_Lean_nullKind;
if (lean_is_scalar(x_378)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_378;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_392);
x_397 = l_Lean_Syntax_setArg(x_387, x_23, x_396);
x_398 = l_Lean_Syntax_setArg(x_381, x_379, x_397);
x_399 = l_Lean_Syntax_setArg(x_386, x_23, x_398);
x_400 = lean_array_set(x_11, x_23, x_399);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_10);
lean_ctor_set(x_401, 1, x_400);
if (lean_is_scalar(x_394)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_394;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_393);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_381);
lean_dec(x_378);
lean_dec(x_11);
lean_dec(x_10);
x_403 = lean_ctor_get(x_391, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_391, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_405 = x_391;
} else {
 lean_dec_ref(x_391);
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
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_381);
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_407 = lean_ctor_get(x_383, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_383, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_409 = x_383;
} else {
 lean_dec_ref(x_383);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
lean_object* x_411; 
lean_dec(x_381);
x_411 = l_Lean_Elab_Term_CollectPatternVars_collect(x_380, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
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
x_415 = l_Lean_Syntax_setArg(x_376, x_379, x_412);
x_416 = lean_array_set(x_11, x_23, x_415);
if (lean_is_scalar(x_378)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_378;
}
lean_ctor_set(x_417, 0, x_10);
lean_ctor_set(x_417, 1, x_416);
if (lean_is_scalar(x_414)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_414;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_413);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_11);
lean_dec(x_10);
x_419 = lean_ctor_get(x_411, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_411, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_421 = x_411;
} else {
 lean_dec_ref(x_411);
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
lean_dec(x_376);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_302);
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_430 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_27);
lean_dec(x_8);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_st_ref_take(x_2, x_432);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_ctor_get(x_434, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_434, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_438 = x_434;
} else {
 lean_dec_ref(x_434);
 x_438 = lean_box(0);
}
x_439 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_431);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
x_441 = lean_array_push(x_437, x_440);
if (lean_is_scalar(x_438)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_438;
}
lean_ctor_set(x_442, 0, x_436);
lean_ctor_set(x_442, 1, x_441);
x_443 = lean_st_ref_set(x_2, x_442, x_435);
lean_dec(x_2);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_445 = x_443;
} else {
 lean_dec_ref(x_443);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_431);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; 
lean_free_object(x_25);
lean_dec(x_1);
x_447 = l_Lean_Syntax_inhabited;
x_448 = lean_array_get(x_447, x_11, x_23);
x_449 = l_Lean_Syntax_isNone(x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_11);
lean_dec(x_10);
x_450 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_451 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_448, x_450, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_302);
lean_dec(x_2);
lean_dec(x_448);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_454 = x_451;
} else {
 lean_dec_ref(x_451);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 2, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_453);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_448);
x_456 = lean_box(0);
x_457 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_11, x_10, x_456, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
return x_457;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_458 = x_1;
} else {
 lean_dec_ref(x_1);
 x_458 = lean_box(0);
}
x_459 = l_Lean_Syntax_inhabited;
x_460 = lean_array_get(x_459, x_11, x_23);
x_461 = l_Lean_Syntax_getArgs(x_460);
lean_dec(x_460);
x_462 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_463 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_461, x_462, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_461);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_466 = x_463;
} else {
 lean_dec_ref(x_463);
 x_466 = lean_box(0);
}
x_467 = l_Lean_nullKind;
if (lean_is_scalar(x_458)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_458;
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_464);
x_469 = lean_array_set(x_11, x_23, x_468);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_10);
lean_ctor_set(x_470, 1, x_469);
if (lean_is_scalar(x_466)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_466;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_465);
return x_471;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_458);
lean_dec(x_11);
lean_dec(x_10);
x_472 = lean_ctor_get(x_463, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_463, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_474 = x_463;
} else {
 lean_dec_ref(x_463);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_472);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
}
}
else
{
lean_object* x_476; lean_object* x_477; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_476 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_477 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_476, x_1, x_2, x_302, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_1);
return x_477;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; 
x_478 = lean_ctor_get(x_25, 1);
lean_inc(x_478);
lean_dec(x_25);
x_479 = lean_ctor_get(x_3, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_3, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_3, 2);
lean_inc(x_481);
x_482 = lean_ctor_get(x_3, 3);
lean_inc(x_482);
x_483 = lean_ctor_get(x_3, 4);
lean_inc(x_483);
x_484 = lean_ctor_get(x_3, 5);
lean_inc(x_484);
x_485 = lean_ctor_get(x_3, 6);
lean_inc(x_485);
x_486 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_487 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_488 = x_3;
} else {
 lean_dec_ref(x_3);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 8, 2);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_479);
lean_ctor_set(x_489, 1, x_480);
lean_ctor_set(x_489, 2, x_481);
lean_ctor_set(x_489, 3, x_482);
lean_ctor_set(x_489, 4, x_483);
lean_ctor_set(x_489, 5, x_484);
lean_ctor_set(x_489, 6, x_485);
lean_ctor_set(x_489, 7, x_22);
lean_ctor_set_uint8(x_489, sizeof(void*)*8, x_486);
lean_ctor_set_uint8(x_489, sizeof(void*)*8 + 1, x_487);
if (x_13 == 0)
{
lean_object* x_490; uint8_t x_491; 
x_490 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_491 = lean_name_eq(x_10, x_490);
if (x_491 == 0)
{
lean_object* x_492; uint8_t x_493; 
x_492 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_493 = lean_name_eq(x_10, x_492);
if (x_493 == 0)
{
lean_object* x_494; uint8_t x_495; 
x_494 = l_Lean_mkHole___closed__2;
x_495 = lean_name_eq(x_10, x_494);
if (x_495 == 0)
{
lean_object* x_496; uint8_t x_497; 
x_496 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_497 = lean_name_eq(x_10, x_496);
if (x_497 == 0)
{
lean_object* x_498; uint8_t x_499; 
lean_dec(x_11);
x_498 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
x_499 = lean_name_eq(x_10, x_498);
if (x_499 == 0)
{
lean_object* x_500; uint8_t x_501; 
x_500 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
x_501 = lean_name_eq(x_10, x_500);
if (x_501 == 0)
{
lean_object* x_502; uint8_t x_503; 
x_502 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_503 = lean_name_eq(x_10, x_502);
if (x_503 == 0)
{
lean_object* x_504; uint8_t x_505; 
x_504 = l_Lean_strLitKind;
x_505 = lean_name_eq(x_10, x_504);
if (x_505 == 0)
{
lean_object* x_506; uint8_t x_507; 
x_506 = l_Lean_numLitKind;
x_507 = lean_name_eq(x_10, x_506);
if (x_507 == 0)
{
lean_object* x_508; uint8_t x_509; 
x_508 = l_Lean_charLitKind;
x_509 = lean_name_eq(x_10, x_508);
if (x_509 == 0)
{
lean_object* x_510; uint8_t x_511; 
x_510 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_511 = lean_name_eq(x_10, x_510);
if (x_511 == 0)
{
lean_object* x_512; uint8_t x_513; 
lean_dec(x_1);
x_512 = l_Lean_choiceKind;
x_513 = lean_name_eq(x_10, x_512);
lean_dec(x_10);
if (x_513 == 0)
{
lean_object* x_514; 
x_514 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
lean_dec(x_2);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; 
x_515 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_516 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_515, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
lean_dec(x_2);
return x_516;
}
}
else
{
lean_object* x_517; 
lean_dec(x_10);
lean_dec(x_2);
x_517 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_517;
}
}
else
{
lean_object* x_518; 
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_1);
lean_ctor_set(x_518, 1, x_478);
return x_518;
}
}
else
{
lean_object* x_519; 
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_1);
lean_ctor_set(x_519, 1, x_478);
return x_519;
}
}
else
{
lean_object* x_520; 
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_1);
lean_ctor_set(x_520, 1, x_478);
return x_520;
}
}
else
{
lean_object* x_521; 
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_1);
lean_ctor_set(x_521, 1, x_478);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_10);
x_522 = lean_unsigned_to_nat(0u);
x_523 = l_Lean_Syntax_getArg(x_1, x_522);
lean_inc(x_7);
lean_inc(x_523);
x_524 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_523, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_526 = lean_unsigned_to_nat(2u);
x_527 = l_Lean_Syntax_getArg(x_1, x_526);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_528 = x_1;
} else {
 lean_dec_ref(x_1);
 x_528 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_489);
x_529 = l_Lean_Elab_Term_CollectPatternVars_collect(x_527, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_525);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = l_Lean_Elab_Term_getCurrMacroScope(x_489, x_4, x_5, x_6, x_7, x_8, x_531);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_534);
lean_dec(x_8);
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
x_539 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_540 = l_Lean_addMacroScope(x_536, x_539, x_533);
x_541 = l_Lean_SourceInfo_inhabited___closed__1;
x_542 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_543 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_544 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
lean_ctor_set(x_544, 2, x_540);
lean_ctor_set(x_544, 3, x_543);
x_545 = l_Array_empty___closed__1;
x_546 = lean_array_push(x_545, x_544);
x_547 = lean_array_push(x_545, x_523);
x_548 = lean_array_push(x_547, x_530);
x_549 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_528)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_528;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
x_551 = lean_array_push(x_546, x_550);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_12);
lean_ctor_set(x_552, 1, x_551);
if (lean_is_scalar(x_538)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_538;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_537);
return x_553;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_528);
lean_dec(x_523);
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_554 = lean_ctor_get(x_529, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_529, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_556 = x_529;
} else {
 lean_dec_ref(x_529);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_523);
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_558 = lean_ctor_get(x_524, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_524, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_560 = x_524;
} else {
 lean_dec_ref(x_524);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
}
lean_ctor_set(x_561, 0, x_558);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_10);
x_562 = lean_unsigned_to_nat(0u);
x_563 = l_Lean_Syntax_getArg(x_1, x_562);
lean_dec(x_1);
x_564 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_565 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_564, x_563, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
return x_565;
}
}
else
{
lean_object* x_566; lean_object* x_567; uint8_t x_568; 
x_566 = l_Lean_Syntax_inhabited;
x_567 = lean_array_get(x_566, x_11, x_23);
x_568 = l_Lean_Syntax_isNone(x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_615; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_569 = x_1;
} else {
 lean_dec_ref(x_1);
 x_569 = lean_box(0);
}
x_570 = lean_unsigned_to_nat(0u);
x_571 = l_Lean_Syntax_getArg(x_567, x_570);
x_572 = l_Lean_Syntax_getArg(x_567, x_23);
x_615 = l_Lean_Syntax_isNone(x_572);
if (x_615 == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; 
x_616 = l_Lean_Syntax_getArg(x_572, x_570);
x_617 = l_Lean_Syntax_getKind(x_616);
x_618 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_619 = lean_name_eq(x_617, x_618);
lean_dec(x_617);
x_573 = x_619;
goto block_614;
}
else
{
uint8_t x_620; 
x_620 = 1;
x_573 = x_620;
goto block_614;
}
block_614:
{
if (x_573 == 0)
{
lean_object* x_574; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_489);
lean_inc(x_2);
x_574 = l_Lean_Elab_Term_CollectPatternVars_collect(x_571, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = l_Lean_Syntax_setArg(x_567, x_570, x_575);
x_578 = l_Lean_Syntax_getArg(x_572, x_570);
x_579 = l_Lean_Syntax_getArg(x_578, x_23);
x_580 = l_Lean_Syntax_getArgs(x_579);
lean_dec(x_579);
x_581 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_582 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_580, x_581, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_576);
lean_dec(x_580);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
x_586 = l_Lean_nullKind;
if (lean_is_scalar(x_569)) {
 x_587 = lean_alloc_ctor(1, 2, 0);
} else {
 x_587 = x_569;
}
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_583);
x_588 = l_Lean_Syntax_setArg(x_578, x_23, x_587);
x_589 = l_Lean_Syntax_setArg(x_572, x_570, x_588);
x_590 = l_Lean_Syntax_setArg(x_577, x_23, x_589);
x_591 = lean_array_set(x_11, x_23, x_590);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_10);
lean_ctor_set(x_592, 1, x_591);
if (lean_is_scalar(x_585)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_585;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_584);
return x_593;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_11);
lean_dec(x_10);
x_594 = lean_ctor_get(x_582, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_582, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_596 = x_582;
} else {
 lean_dec_ref(x_582);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_572);
lean_dec(x_569);
lean_dec(x_567);
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_598 = lean_ctor_get(x_574, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_574, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_600 = x_574;
} else {
 lean_dec_ref(x_574);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_599);
return x_601;
}
}
else
{
lean_object* x_602; 
lean_dec(x_572);
x_602 = l_Lean_Elab_Term_CollectPatternVars_collect(x_571, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_605 = x_602;
} else {
 lean_dec_ref(x_602);
 x_605 = lean_box(0);
}
x_606 = l_Lean_Syntax_setArg(x_567, x_570, x_603);
x_607 = lean_array_set(x_11, x_23, x_606);
if (lean_is_scalar(x_569)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_569;
}
lean_ctor_set(x_608, 0, x_10);
lean_ctor_set(x_608, 1, x_607);
if (lean_is_scalar(x_605)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_605;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_604);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_569);
lean_dec(x_567);
lean_dec(x_11);
lean_dec(x_10);
x_610 = lean_ctor_get(x_602, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_602, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_612 = x_602;
} else {
 lean_dec_ref(x_602);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
}
}
else
{
lean_object* x_621; 
lean_dec(x_567);
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set(x_621, 1, x_478);
return x_621;
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_489);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_622 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_478);
lean_dec(x_8);
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
x_625 = lean_st_ref_take(x_2, x_624);
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
lean_dec(x_625);
x_628 = lean_ctor_get(x_626, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 lean_ctor_release(x_626, 1);
 x_630 = x_626;
} else {
 lean_dec_ref(x_626);
 x_630 = lean_box(0);
}
x_631 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_623);
x_632 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_632, 0, x_631);
x_633 = lean_array_push(x_629, x_632);
if (lean_is_scalar(x_630)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_630;
}
lean_ctor_set(x_634, 0, x_628);
lean_ctor_set(x_634, 1, x_633);
x_635 = lean_st_ref_set(x_2, x_634, x_627);
lean_dec(x_2);
x_636 = lean_ctor_get(x_635, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_637 = x_635;
} else {
 lean_dec_ref(x_635);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_623);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; uint8_t x_641; 
lean_dec(x_1);
x_639 = l_Lean_Syntax_inhabited;
x_640 = lean_array_get(x_639, x_11, x_23);
x_641 = l_Lean_Syntax_isNone(x_640);
if (x_641 == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_11);
lean_dec(x_10);
x_642 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_643 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_640, x_642, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
lean_dec(x_2);
lean_dec(x_640);
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
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_645);
return x_647;
}
else
{
lean_object* x_648; lean_object* x_649; 
lean_dec(x_640);
x_648 = lean_box(0);
x_649 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_11, x_10, x_648, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
return x_649;
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_650 = x_1;
} else {
 lean_dec_ref(x_1);
 x_650 = lean_box(0);
}
x_651 = l_Lean_Syntax_inhabited;
x_652 = lean_array_get(x_651, x_11, x_23);
x_653 = l_Lean_Syntax_getArgs(x_652);
lean_dec(x_652);
x_654 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_655 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_653, x_654, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
lean_dec(x_653);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_658 = x_655;
} else {
 lean_dec_ref(x_655);
 x_658 = lean_box(0);
}
x_659 = l_Lean_nullKind;
if (lean_is_scalar(x_650)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_650;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_656);
x_661 = lean_array_set(x_11, x_23, x_660);
x_662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_662, 0, x_10);
lean_ctor_set(x_662, 1, x_661);
if (lean_is_scalar(x_658)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_658;
}
lean_ctor_set(x_663, 0, x_662);
lean_ctor_set(x_663, 1, x_657);
return x_663;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_650);
lean_dec(x_11);
lean_dec(x_10);
x_664 = lean_ctor_get(x_655, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_655, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_666 = x_655;
} else {
 lean_dec_ref(x_655);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_664);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
}
}
else
{
lean_object* x_668; lean_object* x_669; 
lean_dec(x_11);
lean_dec(x_10);
x_668 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_669 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_668, x_1, x_2, x_489, x_4, x_5, x_6, x_7, x_8, x_478);
lean_dec(x_1);
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; 
x_670 = lean_ctor_get(x_19, 0);
x_671 = lean_ctor_get(x_19, 1);
x_672 = lean_ctor_get(x_19, 2);
x_673 = lean_ctor_get(x_19, 3);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_19);
x_674 = lean_unsigned_to_nat(1u);
x_675 = lean_nat_add(x_671, x_674);
x_676 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_676, 0, x_670);
lean_ctor_set(x_676, 1, x_675);
lean_ctor_set(x_676, 2, x_672);
lean_ctor_set(x_676, 3, x_673);
x_677 = lean_st_ref_set(x_8, x_676, x_20);
x_678 = lean_ctor_get(x_677, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_677)) {
 lean_ctor_release(x_677, 0);
 lean_ctor_release(x_677, 1);
 x_679 = x_677;
} else {
 lean_dec_ref(x_677);
 x_679 = lean_box(0);
}
x_680 = lean_ctor_get(x_3, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_3, 1);
lean_inc(x_681);
x_682 = lean_ctor_get(x_3, 2);
lean_inc(x_682);
x_683 = lean_ctor_get(x_3, 3);
lean_inc(x_683);
x_684 = lean_ctor_get(x_3, 4);
lean_inc(x_684);
x_685 = lean_ctor_get(x_3, 5);
lean_inc(x_685);
x_686 = lean_ctor_get(x_3, 6);
lean_inc(x_686);
x_687 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_688 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_689 = x_3;
} else {
 lean_dec_ref(x_3);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(0, 8, 2);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_680);
lean_ctor_set(x_690, 1, x_681);
lean_ctor_set(x_690, 2, x_682);
lean_ctor_set(x_690, 3, x_683);
lean_ctor_set(x_690, 4, x_684);
lean_ctor_set(x_690, 5, x_685);
lean_ctor_set(x_690, 6, x_686);
lean_ctor_set(x_690, 7, x_671);
lean_ctor_set_uint8(x_690, sizeof(void*)*8, x_687);
lean_ctor_set_uint8(x_690, sizeof(void*)*8 + 1, x_688);
if (x_13 == 0)
{
lean_object* x_691; uint8_t x_692; 
x_691 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_692 = lean_name_eq(x_10, x_691);
if (x_692 == 0)
{
lean_object* x_693; uint8_t x_694; 
x_693 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_694 = lean_name_eq(x_10, x_693);
if (x_694 == 0)
{
lean_object* x_695; uint8_t x_696; 
x_695 = l_Lean_mkHole___closed__2;
x_696 = lean_name_eq(x_10, x_695);
if (x_696 == 0)
{
lean_object* x_697; uint8_t x_698; 
x_697 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_698 = lean_name_eq(x_10, x_697);
if (x_698 == 0)
{
lean_object* x_699; uint8_t x_700; 
lean_dec(x_11);
x_699 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
x_700 = lean_name_eq(x_10, x_699);
if (x_700 == 0)
{
lean_object* x_701; uint8_t x_702; 
x_701 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
x_702 = lean_name_eq(x_10, x_701);
if (x_702 == 0)
{
lean_object* x_703; uint8_t x_704; 
x_703 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_704 = lean_name_eq(x_10, x_703);
if (x_704 == 0)
{
lean_object* x_705; uint8_t x_706; 
x_705 = l_Lean_strLitKind;
x_706 = lean_name_eq(x_10, x_705);
if (x_706 == 0)
{
lean_object* x_707; uint8_t x_708; 
x_707 = l_Lean_numLitKind;
x_708 = lean_name_eq(x_10, x_707);
if (x_708 == 0)
{
lean_object* x_709; uint8_t x_710; 
x_709 = l_Lean_charLitKind;
x_710 = lean_name_eq(x_10, x_709);
if (x_710 == 0)
{
lean_object* x_711; uint8_t x_712; 
lean_dec(x_679);
x_711 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_712 = lean_name_eq(x_10, x_711);
if (x_712 == 0)
{
lean_object* x_713; uint8_t x_714; 
lean_dec(x_1);
x_713 = l_Lean_choiceKind;
x_714 = lean_name_eq(x_10, x_713);
lean_dec(x_10);
if (x_714 == 0)
{
lean_object* x_715; 
x_715 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_690);
lean_dec(x_2);
return x_715;
}
else
{
lean_object* x_716; lean_object* x_717; 
x_716 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_717 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_716, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_690);
lean_dec(x_2);
return x_717;
}
}
else
{
lean_object* x_718; 
lean_dec(x_10);
lean_dec(x_2);
x_718 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_718;
}
}
else
{
lean_object* x_719; 
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_679)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_679;
}
lean_ctor_set(x_719, 0, x_1);
lean_ctor_set(x_719, 1, x_678);
return x_719;
}
}
else
{
lean_object* x_720; 
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_679)) {
 x_720 = lean_alloc_ctor(0, 2, 0);
} else {
 x_720 = x_679;
}
lean_ctor_set(x_720, 0, x_1);
lean_ctor_set(x_720, 1, x_678);
return x_720;
}
}
else
{
lean_object* x_721; 
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_679)) {
 x_721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_721 = x_679;
}
lean_ctor_set(x_721, 0, x_1);
lean_ctor_set(x_721, 1, x_678);
return x_721;
}
}
else
{
lean_object* x_722; 
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_679)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_679;
}
lean_ctor_set(x_722, 0, x_1);
lean_ctor_set(x_722, 1, x_678);
return x_722;
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_679);
lean_dec(x_10);
x_723 = lean_unsigned_to_nat(0u);
x_724 = l_Lean_Syntax_getArg(x_1, x_723);
lean_inc(x_7);
lean_inc(x_724);
x_725 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_724, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
x_727 = lean_unsigned_to_nat(2u);
x_728 = l_Lean_Syntax_getArg(x_1, x_727);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_729 = x_1;
} else {
 lean_dec_ref(x_1);
 x_729 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_690);
x_730 = l_Lean_Elab_Term_CollectPatternVars_collect(x_728, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_726);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_733 = l_Lean_Elab_Term_getCurrMacroScope(x_690, x_4, x_5, x_6, x_7, x_8, x_732);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_690);
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
x_736 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_735);
lean_dec(x_8);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_739 = x_736;
} else {
 lean_dec_ref(x_736);
 x_739 = lean_box(0);
}
x_740 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_741 = l_Lean_addMacroScope(x_737, x_740, x_734);
x_742 = l_Lean_SourceInfo_inhabited___closed__1;
x_743 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_744 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_745 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
lean_ctor_set(x_745, 2, x_741);
lean_ctor_set(x_745, 3, x_744);
x_746 = l_Array_empty___closed__1;
x_747 = lean_array_push(x_746, x_745);
x_748 = lean_array_push(x_746, x_724);
x_749 = lean_array_push(x_748, x_731);
x_750 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_729)) {
 x_751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_751 = x_729;
}
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set(x_751, 1, x_749);
x_752 = lean_array_push(x_747, x_751);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_12);
lean_ctor_set(x_753, 1, x_752);
if (lean_is_scalar(x_739)) {
 x_754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_754 = x_739;
}
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_738);
return x_754;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_729);
lean_dec(x_724);
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_755 = lean_ctor_get(x_730, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_730, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_757 = x_730;
} else {
 lean_dec_ref(x_730);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_724);
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_759 = lean_ctor_get(x_725, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_725, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_761 = x_725;
} else {
 lean_dec_ref(x_725);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_679);
lean_dec(x_10);
x_763 = lean_unsigned_to_nat(0u);
x_764 = l_Lean_Syntax_getArg(x_1, x_763);
lean_dec(x_1);
x_765 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_766 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_765, x_764, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
return x_766;
}
}
else
{
lean_object* x_767; lean_object* x_768; uint8_t x_769; 
x_767 = l_Lean_Syntax_inhabited;
x_768 = lean_array_get(x_767, x_11, x_674);
x_769 = l_Lean_Syntax_isNone(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; uint8_t x_774; uint8_t x_816; 
lean_dec(x_679);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_770 = x_1;
} else {
 lean_dec_ref(x_1);
 x_770 = lean_box(0);
}
x_771 = lean_unsigned_to_nat(0u);
x_772 = l_Lean_Syntax_getArg(x_768, x_771);
x_773 = l_Lean_Syntax_getArg(x_768, x_674);
x_816 = l_Lean_Syntax_isNone(x_773);
if (x_816 == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; 
x_817 = l_Lean_Syntax_getArg(x_773, x_771);
x_818 = l_Lean_Syntax_getKind(x_817);
x_819 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_820 = lean_name_eq(x_818, x_819);
lean_dec(x_818);
x_774 = x_820;
goto block_815;
}
else
{
uint8_t x_821; 
x_821 = 1;
x_774 = x_821;
goto block_815;
}
block_815:
{
if (x_774 == 0)
{
lean_object* x_775; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_690);
lean_inc(x_2);
x_775 = l_Lean_Elab_Term_CollectPatternVars_collect(x_772, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = l_Lean_Syntax_setArg(x_768, x_771, x_776);
x_779 = l_Lean_Syntax_getArg(x_773, x_771);
x_780 = l_Lean_Syntax_getArg(x_779, x_674);
x_781 = l_Lean_Syntax_getArgs(x_780);
lean_dec(x_780);
x_782 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_783 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_781, x_782, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_777);
lean_dec(x_781);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_786 = x_783;
} else {
 lean_dec_ref(x_783);
 x_786 = lean_box(0);
}
x_787 = l_Lean_nullKind;
if (lean_is_scalar(x_770)) {
 x_788 = lean_alloc_ctor(1, 2, 0);
} else {
 x_788 = x_770;
}
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_784);
x_789 = l_Lean_Syntax_setArg(x_779, x_674, x_788);
x_790 = l_Lean_Syntax_setArg(x_773, x_771, x_789);
x_791 = l_Lean_Syntax_setArg(x_778, x_674, x_790);
x_792 = lean_array_set(x_11, x_674, x_791);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_10);
lean_ctor_set(x_793, 1, x_792);
if (lean_is_scalar(x_786)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_786;
}
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_785);
return x_794;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_773);
lean_dec(x_770);
lean_dec(x_11);
lean_dec(x_10);
x_795 = lean_ctor_get(x_783, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_783, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_797 = x_783;
} else {
 lean_dec_ref(x_783);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_795);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_773);
lean_dec(x_770);
lean_dec(x_768);
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_799 = lean_ctor_get(x_775, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_775, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_801 = x_775;
} else {
 lean_dec_ref(x_775);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 2, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_800);
return x_802;
}
}
else
{
lean_object* x_803; 
lean_dec(x_773);
x_803 = l_Lean_Elab_Term_CollectPatternVars_collect(x_772, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_806 = x_803;
} else {
 lean_dec_ref(x_803);
 x_806 = lean_box(0);
}
x_807 = l_Lean_Syntax_setArg(x_768, x_771, x_804);
x_808 = lean_array_set(x_11, x_674, x_807);
if (lean_is_scalar(x_770)) {
 x_809 = lean_alloc_ctor(1, 2, 0);
} else {
 x_809 = x_770;
}
lean_ctor_set(x_809, 0, x_10);
lean_ctor_set(x_809, 1, x_808);
if (lean_is_scalar(x_806)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_806;
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_805);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_770);
lean_dec(x_768);
lean_dec(x_11);
lean_dec(x_10);
x_811 = lean_ctor_get(x_803, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_803, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_813 = x_803;
} else {
 lean_dec_ref(x_803);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
}
}
else
{
lean_object* x_822; 
lean_dec(x_768);
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_679)) {
 x_822 = lean_alloc_ctor(0, 2, 0);
} else {
 x_822 = x_679;
}
lean_ctor_set(x_822, 0, x_1);
lean_ctor_set(x_822, 1, x_678);
return x_822;
}
}
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_dec(x_690);
lean_dec(x_679);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_823 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_678);
lean_dec(x_8);
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_823, 1);
lean_inc(x_825);
lean_dec(x_823);
x_826 = lean_st_ref_take(x_2, x_825);
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_ctor_get(x_827, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_827, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_831 = x_827;
} else {
 lean_dec_ref(x_827);
 x_831 = lean_box(0);
}
x_832 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_824);
x_833 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_833, 0, x_832);
x_834 = lean_array_push(x_830, x_833);
if (lean_is_scalar(x_831)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_831;
}
lean_ctor_set(x_835, 0, x_829);
lean_ctor_set(x_835, 1, x_834);
x_836 = lean_st_ref_set(x_2, x_835, x_828);
lean_dec(x_2);
x_837 = lean_ctor_get(x_836, 1);
lean_inc(x_837);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 lean_ctor_release(x_836, 1);
 x_838 = x_836;
} else {
 lean_dec_ref(x_836);
 x_838 = lean_box(0);
}
if (lean_is_scalar(x_838)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_838;
}
lean_ctor_set(x_839, 0, x_824);
lean_ctor_set(x_839, 1, x_837);
return x_839;
}
}
else
{
lean_object* x_840; lean_object* x_841; uint8_t x_842; 
lean_dec(x_679);
lean_dec(x_1);
x_840 = l_Lean_Syntax_inhabited;
x_841 = lean_array_get(x_840, x_11, x_674);
x_842 = l_Lean_Syntax_isNone(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_11);
lean_dec(x_10);
x_843 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_844 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_841, x_843, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_690);
lean_dec(x_2);
lean_dec(x_841);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_847 = x_844;
} else {
 lean_dec_ref(x_844);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_848 = x_847;
}
lean_ctor_set(x_848, 0, x_845);
lean_ctor_set(x_848, 1, x_846);
return x_848;
}
else
{
lean_object* x_849; lean_object* x_850; 
lean_dec(x_841);
x_849 = lean_box(0);
x_850 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_11, x_10, x_849, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
return x_850;
}
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_679);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_851 = x_1;
} else {
 lean_dec_ref(x_1);
 x_851 = lean_box(0);
}
x_852 = l_Lean_Syntax_inhabited;
x_853 = lean_array_get(x_852, x_11, x_674);
x_854 = l_Lean_Syntax_getArgs(x_853);
lean_dec(x_853);
x_855 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_856 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_854, x_855, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_854);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_856, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 lean_ctor_release(x_856, 1);
 x_859 = x_856;
} else {
 lean_dec_ref(x_856);
 x_859 = lean_box(0);
}
x_860 = l_Lean_nullKind;
if (lean_is_scalar(x_851)) {
 x_861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_861 = x_851;
}
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_857);
x_862 = lean_array_set(x_11, x_674, x_861);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_10);
lean_ctor_set(x_863, 1, x_862);
if (lean_is_scalar(x_859)) {
 x_864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_864 = x_859;
}
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_858);
return x_864;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_851);
lean_dec(x_11);
lean_dec(x_10);
x_865 = lean_ctor_get(x_856, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_856, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 lean_ctor_release(x_856, 1);
 x_867 = x_856;
} else {
 lean_dec_ref(x_856);
 x_867 = lean_box(0);
}
if (lean_is_scalar(x_867)) {
 x_868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_868 = x_867;
}
lean_ctor_set(x_868, 0, x_865);
lean_ctor_set(x_868, 1, x_866);
return x_868;
}
}
}
else
{
lean_object* x_869; lean_object* x_870; 
lean_dec(x_679);
lean_dec(x_11);
lean_dec(x_10);
x_869 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_870 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_869, x_1, x_2, x_690, x_4, x_5, x_6, x_7, x_8, x_678);
lean_dec(x_1);
return x_870;
}
}
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; uint8_t x_899; uint8_t x_900; lean_object* x_901; lean_object* x_902; 
x_871 = lean_ctor_get(x_7, 0);
x_872 = lean_ctor_get(x_7, 1);
x_873 = lean_ctor_get(x_7, 2);
x_874 = lean_ctor_get(x_7, 3);
lean_inc(x_874);
lean_inc(x_873);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_7);
x_875 = l_Lean_replaceRef(x_1, x_874);
x_876 = l_Lean_replaceRef(x_875, x_874);
lean_dec(x_874);
lean_dec(x_875);
x_877 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_877, 0, x_871);
lean_ctor_set(x_877, 1, x_872);
lean_ctor_set(x_877, 2, x_873);
lean_ctor_set(x_877, 3, x_876);
x_878 = lean_st_ref_take(x_8, x_9);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_ctor_get(x_879, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_879, 1);
lean_inc(x_882);
x_883 = lean_ctor_get(x_879, 2);
lean_inc(x_883);
x_884 = lean_ctor_get(x_879, 3);
lean_inc(x_884);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 lean_ctor_release(x_879, 1);
 lean_ctor_release(x_879, 2);
 lean_ctor_release(x_879, 3);
 x_885 = x_879;
} else {
 lean_dec_ref(x_879);
 x_885 = lean_box(0);
}
x_886 = lean_unsigned_to_nat(1u);
x_887 = lean_nat_add(x_882, x_886);
if (lean_is_scalar(x_885)) {
 x_888 = lean_alloc_ctor(0, 4, 0);
} else {
 x_888 = x_885;
}
lean_ctor_set(x_888, 0, x_881);
lean_ctor_set(x_888, 1, x_887);
lean_ctor_set(x_888, 2, x_883);
lean_ctor_set(x_888, 3, x_884);
x_889 = lean_st_ref_set(x_8, x_888, x_880);
x_890 = lean_ctor_get(x_889, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_891 = x_889;
} else {
 lean_dec_ref(x_889);
 x_891 = lean_box(0);
}
x_892 = lean_ctor_get(x_3, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_3, 1);
lean_inc(x_893);
x_894 = lean_ctor_get(x_3, 2);
lean_inc(x_894);
x_895 = lean_ctor_get(x_3, 3);
lean_inc(x_895);
x_896 = lean_ctor_get(x_3, 4);
lean_inc(x_896);
x_897 = lean_ctor_get(x_3, 5);
lean_inc(x_897);
x_898 = lean_ctor_get(x_3, 6);
lean_inc(x_898);
x_899 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_900 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_901 = x_3;
} else {
 lean_dec_ref(x_3);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(0, 8, 2);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_892);
lean_ctor_set(x_902, 1, x_893);
lean_ctor_set(x_902, 2, x_894);
lean_ctor_set(x_902, 3, x_895);
lean_ctor_set(x_902, 4, x_896);
lean_ctor_set(x_902, 5, x_897);
lean_ctor_set(x_902, 6, x_898);
lean_ctor_set(x_902, 7, x_882);
lean_ctor_set_uint8(x_902, sizeof(void*)*8, x_899);
lean_ctor_set_uint8(x_902, sizeof(void*)*8 + 1, x_900);
if (x_13 == 0)
{
lean_object* x_903; uint8_t x_904; 
x_903 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_904 = lean_name_eq(x_10, x_903);
if (x_904 == 0)
{
lean_object* x_905; uint8_t x_906; 
x_905 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_906 = lean_name_eq(x_10, x_905);
if (x_906 == 0)
{
lean_object* x_907; uint8_t x_908; 
x_907 = l_Lean_mkHole___closed__2;
x_908 = lean_name_eq(x_10, x_907);
if (x_908 == 0)
{
lean_object* x_909; uint8_t x_910; 
x_909 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_910 = lean_name_eq(x_10, x_909);
if (x_910 == 0)
{
lean_object* x_911; uint8_t x_912; 
lean_dec(x_11);
x_911 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
x_912 = lean_name_eq(x_10, x_911);
if (x_912 == 0)
{
lean_object* x_913; uint8_t x_914; 
x_913 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
x_914 = lean_name_eq(x_10, x_913);
if (x_914 == 0)
{
lean_object* x_915; uint8_t x_916; 
x_915 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_916 = lean_name_eq(x_10, x_915);
if (x_916 == 0)
{
lean_object* x_917; uint8_t x_918; 
x_917 = l_Lean_strLitKind;
x_918 = lean_name_eq(x_10, x_917);
if (x_918 == 0)
{
lean_object* x_919; uint8_t x_920; 
x_919 = l_Lean_numLitKind;
x_920 = lean_name_eq(x_10, x_919);
if (x_920 == 0)
{
lean_object* x_921; uint8_t x_922; 
x_921 = l_Lean_charLitKind;
x_922 = lean_name_eq(x_10, x_921);
if (x_922 == 0)
{
lean_object* x_923; uint8_t x_924; 
lean_dec(x_891);
x_923 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_924 = lean_name_eq(x_10, x_923);
if (x_924 == 0)
{
lean_object* x_925; uint8_t x_926; 
lean_dec(x_1);
x_925 = l_Lean_choiceKind;
x_926 = lean_name_eq(x_10, x_925);
lean_dec(x_10);
if (x_926 == 0)
{
lean_object* x_927; 
x_927 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
lean_dec(x_8);
lean_dec(x_877);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_902);
lean_dec(x_2);
return x_927;
}
else
{
lean_object* x_928; lean_object* x_929; 
x_928 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_929 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___rarg(x_928, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
lean_dec(x_8);
lean_dec(x_877);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_902);
lean_dec(x_2);
return x_929;
}
}
else
{
lean_object* x_930; 
lean_dec(x_10);
lean_dec(x_2);
x_930 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
lean_dec(x_8);
lean_dec(x_877);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_930;
}
}
else
{
lean_object* x_931; 
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_891)) {
 x_931 = lean_alloc_ctor(0, 2, 0);
} else {
 x_931 = x_891;
}
lean_ctor_set(x_931, 0, x_1);
lean_ctor_set(x_931, 1, x_890);
return x_931;
}
}
else
{
lean_object* x_932; 
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_891)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_891;
}
lean_ctor_set(x_932, 0, x_1);
lean_ctor_set(x_932, 1, x_890);
return x_932;
}
}
else
{
lean_object* x_933; 
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_891)) {
 x_933 = lean_alloc_ctor(0, 2, 0);
} else {
 x_933 = x_891;
}
lean_ctor_set(x_933, 0, x_1);
lean_ctor_set(x_933, 1, x_890);
return x_933;
}
}
else
{
lean_object* x_934; 
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_891)) {
 x_934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_934 = x_891;
}
lean_ctor_set(x_934, 0, x_1);
lean_ctor_set(x_934, 1, x_890);
return x_934;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
lean_dec(x_891);
lean_dec(x_10);
x_935 = lean_unsigned_to_nat(0u);
x_936 = l_Lean_Syntax_getArg(x_1, x_935);
lean_inc(x_877);
lean_inc(x_936);
x_937 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_936, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_938 = lean_ctor_get(x_937, 1);
lean_inc(x_938);
lean_dec(x_937);
x_939 = lean_unsigned_to_nat(2u);
x_940 = l_Lean_Syntax_getArg(x_1, x_939);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_941 = x_1;
} else {
 lean_dec_ref(x_1);
 x_941 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_877);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_902);
x_942 = l_Lean_Elab_Term_CollectPatternVars_collect(x_940, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_938);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
lean_dec(x_942);
x_945 = l_Lean_Elab_Term_getCurrMacroScope(x_902, x_4, x_5, x_6, x_877, x_8, x_944);
lean_dec(x_877);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_902);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_947);
lean_dec(x_8);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_951 = x_948;
} else {
 lean_dec_ref(x_948);
 x_951 = lean_box(0);
}
x_952 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_953 = l_Lean_addMacroScope(x_949, x_952, x_946);
x_954 = l_Lean_SourceInfo_inhabited___closed__1;
x_955 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_956 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_957 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_957, 0, x_954);
lean_ctor_set(x_957, 1, x_955);
lean_ctor_set(x_957, 2, x_953);
lean_ctor_set(x_957, 3, x_956);
x_958 = l_Array_empty___closed__1;
x_959 = lean_array_push(x_958, x_957);
x_960 = lean_array_push(x_958, x_936);
x_961 = lean_array_push(x_960, x_943);
x_962 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_941)) {
 x_963 = lean_alloc_ctor(1, 2, 0);
} else {
 x_963 = x_941;
}
lean_ctor_set(x_963, 0, x_962);
lean_ctor_set(x_963, 1, x_961);
x_964 = lean_array_push(x_959, x_963);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_12);
lean_ctor_set(x_965, 1, x_964);
if (lean_is_scalar(x_951)) {
 x_966 = lean_alloc_ctor(0, 2, 0);
} else {
 x_966 = x_951;
}
lean_ctor_set(x_966, 0, x_965);
lean_ctor_set(x_966, 1, x_950);
return x_966;
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_941);
lean_dec(x_936);
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_967 = lean_ctor_get(x_942, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_942, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_969 = x_942;
} else {
 lean_dec_ref(x_942);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_967);
lean_ctor_set(x_970, 1, x_968);
return x_970;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_936);
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_971 = lean_ctor_get(x_937, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_937, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_937)) {
 lean_ctor_release(x_937, 0);
 lean_ctor_release(x_937, 1);
 x_973 = x_937;
} else {
 lean_dec_ref(x_937);
 x_973 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_974 = x_973;
}
lean_ctor_set(x_974, 0, x_971);
lean_ctor_set(x_974, 1, x_972);
return x_974;
}
}
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_891);
lean_dec(x_10);
x_975 = lean_unsigned_to_nat(0u);
x_976 = l_Lean_Syntax_getArg(x_1, x_975);
lean_dec(x_1);
x_977 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_978 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_977, x_976, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
return x_978;
}
}
else
{
lean_object* x_979; lean_object* x_980; uint8_t x_981; 
x_979 = l_Lean_Syntax_inhabited;
x_980 = lean_array_get(x_979, x_11, x_886);
x_981 = l_Lean_Syntax_isNone(x_980);
if (x_981 == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; uint8_t x_986; uint8_t x_1028; 
lean_dec(x_891);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_982 = x_1;
} else {
 lean_dec_ref(x_1);
 x_982 = lean_box(0);
}
x_983 = lean_unsigned_to_nat(0u);
x_984 = l_Lean_Syntax_getArg(x_980, x_983);
x_985 = l_Lean_Syntax_getArg(x_980, x_886);
x_1028 = l_Lean_Syntax_isNone(x_985);
if (x_1028 == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; uint8_t x_1032; 
x_1029 = l_Lean_Syntax_getArg(x_985, x_983);
x_1030 = l_Lean_Syntax_getKind(x_1029);
x_1031 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_1032 = lean_name_eq(x_1030, x_1031);
lean_dec(x_1030);
x_986 = x_1032;
goto block_1027;
}
else
{
uint8_t x_1033; 
x_1033 = 1;
x_986 = x_1033;
goto block_1027;
}
block_1027:
{
if (x_986 == 0)
{
lean_object* x_987; 
lean_inc(x_8);
lean_inc(x_877);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_902);
lean_inc(x_2);
x_987 = l_Lean_Elab_Term_CollectPatternVars_collect(x_984, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_987, 1);
lean_inc(x_989);
lean_dec(x_987);
x_990 = l_Lean_Syntax_setArg(x_980, x_983, x_988);
x_991 = l_Lean_Syntax_getArg(x_985, x_983);
x_992 = l_Lean_Syntax_getArg(x_991, x_886);
x_993 = l_Lean_Syntax_getArgs(x_992);
lean_dec(x_992);
x_994 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_995 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_993, x_994, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_989);
lean_dec(x_993);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_998 = x_995;
} else {
 lean_dec_ref(x_995);
 x_998 = lean_box(0);
}
x_999 = l_Lean_nullKind;
if (lean_is_scalar(x_982)) {
 x_1000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1000 = x_982;
}
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_996);
x_1001 = l_Lean_Syntax_setArg(x_991, x_886, x_1000);
x_1002 = l_Lean_Syntax_setArg(x_985, x_983, x_1001);
x_1003 = l_Lean_Syntax_setArg(x_990, x_886, x_1002);
x_1004 = lean_array_set(x_11, x_886, x_1003);
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_10);
lean_ctor_set(x_1005, 1, x_1004);
if (lean_is_scalar(x_998)) {
 x_1006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1006 = x_998;
}
lean_ctor_set(x_1006, 0, x_1005);
lean_ctor_set(x_1006, 1, x_997);
return x_1006;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_991);
lean_dec(x_990);
lean_dec(x_985);
lean_dec(x_982);
lean_dec(x_11);
lean_dec(x_10);
x_1007 = lean_ctor_get(x_995, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_995, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_1009 = x_995;
} else {
 lean_dec_ref(x_995);
 x_1009 = lean_box(0);
}
if (lean_is_scalar(x_1009)) {
 x_1010 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1010 = x_1009;
}
lean_ctor_set(x_1010, 0, x_1007);
lean_ctor_set(x_1010, 1, x_1008);
return x_1010;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_985);
lean_dec(x_982);
lean_dec(x_980);
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1011 = lean_ctor_get(x_987, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_987, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_987)) {
 lean_ctor_release(x_987, 0);
 lean_ctor_release(x_987, 1);
 x_1013 = x_987;
} else {
 lean_dec_ref(x_987);
 x_1013 = lean_box(0);
}
if (lean_is_scalar(x_1013)) {
 x_1014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1014 = x_1013;
}
lean_ctor_set(x_1014, 0, x_1011);
lean_ctor_set(x_1014, 1, x_1012);
return x_1014;
}
}
else
{
lean_object* x_1015; 
lean_dec(x_985);
x_1015 = l_Lean_Elab_Term_CollectPatternVars_collect(x_984, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1018 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1018 = lean_box(0);
}
x_1019 = l_Lean_Syntax_setArg(x_980, x_983, x_1016);
x_1020 = lean_array_set(x_11, x_886, x_1019);
if (lean_is_scalar(x_982)) {
 x_1021 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1021 = x_982;
}
lean_ctor_set(x_1021, 0, x_10);
lean_ctor_set(x_1021, 1, x_1020);
if (lean_is_scalar(x_1018)) {
 x_1022 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1022 = x_1018;
}
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_1017);
return x_1022;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_982);
lean_dec(x_980);
lean_dec(x_11);
lean_dec(x_10);
x_1023 = lean_ctor_get(x_1015, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1015, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1025 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1025 = lean_box(0);
}
if (lean_is_scalar(x_1025)) {
 x_1026 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1026 = x_1025;
}
lean_ctor_set(x_1026, 0, x_1023);
lean_ctor_set(x_1026, 1, x_1024);
return x_1026;
}
}
}
}
else
{
lean_object* x_1034; 
lean_dec(x_980);
lean_dec(x_902);
lean_dec(x_877);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_891)) {
 x_1034 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1034 = x_891;
}
lean_ctor_set(x_1034, 0, x_1);
lean_ctor_set(x_1034, 1, x_890);
return x_1034;
}
}
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_902);
lean_dec(x_891);
lean_dec(x_877);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1035 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_890);
lean_dec(x_8);
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
lean_dec(x_1035);
x_1038 = lean_st_ref_take(x_2, x_1037);
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec(x_1038);
x_1041 = lean_ctor_get(x_1039, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1039, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1039)) {
 lean_ctor_release(x_1039, 0);
 lean_ctor_release(x_1039, 1);
 x_1043 = x_1039;
} else {
 lean_dec_ref(x_1039);
 x_1043 = lean_box(0);
}
x_1044 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_1036);
x_1045 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1045, 0, x_1044);
x_1046 = lean_array_push(x_1042, x_1045);
if (lean_is_scalar(x_1043)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1043;
}
lean_ctor_set(x_1047, 0, x_1041);
lean_ctor_set(x_1047, 1, x_1046);
x_1048 = lean_st_ref_set(x_2, x_1047, x_1040);
lean_dec(x_2);
x_1049 = lean_ctor_get(x_1048, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 x_1050 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1036);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; uint8_t x_1054; 
lean_dec(x_891);
lean_dec(x_1);
x_1052 = l_Lean_Syntax_inhabited;
x_1053 = lean_array_get(x_1052, x_11, x_886);
x_1054 = l_Lean_Syntax_isNone(x_1053);
if (x_1054 == 0)
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_11);
lean_dec(x_10);
x_1055 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_1056 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_1053, x_1055, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_902);
lean_dec(x_2);
lean_dec(x_1053);
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1059 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1057);
lean_ctor_set(x_1060, 1, x_1058);
return x_1060;
}
else
{
lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_1053);
x_1061 = lean_box(0);
x_1062 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_11, x_10, x_1061, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
return x_1062;
}
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_891);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1063 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1063 = lean_box(0);
}
x_1064 = l_Lean_Syntax_inhabited;
x_1065 = lean_array_get(x_1064, x_11, x_886);
x_1066 = l_Lean_Syntax_getArgs(x_1065);
lean_dec(x_1065);
x_1067 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1068 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_1066, x_1067, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
lean_dec(x_1066);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 lean_ctor_release(x_1068, 1);
 x_1071 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1071 = lean_box(0);
}
x_1072 = l_Lean_nullKind;
if (lean_is_scalar(x_1063)) {
 x_1073 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1073 = x_1063;
}
lean_ctor_set(x_1073, 0, x_1072);
lean_ctor_set(x_1073, 1, x_1069);
x_1074 = lean_array_set(x_11, x_886, x_1073);
x_1075 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1075, 0, x_10);
lean_ctor_set(x_1075, 1, x_1074);
if (lean_is_scalar(x_1071)) {
 x_1076 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1076 = x_1071;
}
lean_ctor_set(x_1076, 0, x_1075);
lean_ctor_set(x_1076, 1, x_1070);
return x_1076;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_1063);
lean_dec(x_11);
lean_dec(x_10);
x_1077 = lean_ctor_get(x_1068, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1068, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 lean_ctor_release(x_1068, 1);
 x_1079 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1079 = lean_box(0);
}
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1077);
lean_ctor_set(x_1080, 1, x_1078);
return x_1080;
}
}
}
else
{
lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_891);
lean_dec(x_11);
lean_dec(x_10);
x_1081 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1082 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_1081, x_1, x_2, x_902, x_4, x_5, x_6, x_877, x_8, x_890);
lean_dec(x_1);
return x_1082;
}
}
}
case 3:
{
lean_object* x_1083; lean_object* x_1084; 
x_1083 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1084 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(x_1083, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1084;
}
default: 
{
lean_object* x_1085; 
lean_dec(x_1);
x_1085 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1085;
}
}
}
}
lean_object* l___private_Init_LeanInit_17__mapSepElemsMAux___main___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_LeanInit_17__mapSepElemsMAux___main___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("collecting variables at pattern: ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
x_54 = lean_st_ref_get(x_9, x_10);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = 0;
x_19 = x_59;
x_20 = x_58;
goto block_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_62 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_19 = x_65;
x_20 = x_64;
goto block_53;
}
block_53:
{
if (x_19 == 0)
{
lean_object* x_21; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Elab_Term_CollectPatternVars_collect(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
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
x_27 = lean_array_fset(x_17, x_1, x_26);
lean_dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_9);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_18);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_18);
x_34 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_39 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_38, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l_Lean_Elab_Term_CollectPatternVars_collect(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_1, x_44);
x_46 = x_42;
x_47 = lean_array_fset(x_17, x_1, x_46);
lean_dec(x_1);
x_1 = x_45;
x_2 = x_47;
x_10 = x_43;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = x_12;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3), 10, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = x_16;
x_18 = lean_apply_8(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_31 = x_29;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3), 10, 2);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_31);
x_34 = x_33;
x_35 = lean_apply_8(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_30);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
lean_dec(x_28);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Elab_Term_CollectPatternVars_main(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Elab_Term_getPatternVars_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_getPatternVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getPatternVars_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_st_ref_get(x_7, x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_st_ref_get(x_7, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_33);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_43, 0, x_33);
x_44 = x_43;
x_45 = lean_environment_main_module(x_33);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_38);
x_47 = l_Lean_expandMacros___main(x_1, x_46, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_take(x_7, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 1);
lean_dec(x_54);
lean_ctor_set(x_51, 1, x_49);
x_55 = lean_st_ref_set(x_7, x_51, x_52);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_9 = x_48;
x_10 = x_56;
goto block_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 2);
x_59 = lean_ctor_get(x_51, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_st_ref_set(x_7, x_60, x_52);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_9 = x_48;
x_10 = x_62;
goto block_29;
}
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
lean_dec(x_47);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_64, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_64);
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
else
{
lean_object* x_73; uint8_t x_74; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2___rarg(x_41);
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
block_29:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect(x_9, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getPatternsVars_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1___rarg), 1, 0);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_26; 
x_26 = x_3 < x_2;
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_4);
x_28 = lean_array_uget(x_1, x_3);
x_29 = lean_st_ref_get(x_11, x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_10, 2);
lean_inc(x_37);
x_38 = lean_st_ref_get(x_11, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_32);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_42, 0, x_32);
x_43 = x_42;
x_44 = lean_environment_main_module(x_32);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_37);
x_46 = l_Lean_expandMacros___main(x_28, x_45, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_take(x_11, x_40);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 1);
lean_dec(x_53);
lean_ctor_set(x_50, 1, x_48);
x_54 = lean_st_ref_set(x_11, x_50, x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_13 = x_47;
x_14 = x_55;
goto block_25;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 2);
x_58 = lean_ctor_get(x_50, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_48);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
x_60 = lean_st_ref_set(x_11, x_59, x_51);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_13 = x_47;
x_14 = x_61;
goto block_25;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_46, 0);
lean_inc(x_62);
lean_dec(x_46);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___rarg(x_63, x_66, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_63);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1___rarg(x_40);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
block_25:
{
lean_object* x_15; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = x_3 + x_17;
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_12 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
x_13 = lean_st_mk_ref(x_12, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_14);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__2(x_1, x_10, x_11, x_16, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_14);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__2(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_getPatternsVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_mkFreshExprMVarWithIdImpl(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_mkFVar(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = 0;
x_23 = lean_box(0);
lean_inc(x_5);
x_24 = l_Lean_Meta_mkFreshExprMVarWithIdImpl(x_15, x_21, x_22, x_23, x_5, x_6, x_7, x_8, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_2 = x_27;
x_9 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
lean_dec(x_2);
x_2 = x_34;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = l_Lean_Expr_fvarId_x21(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_array_push(x_2, x_16);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(x_3, x_4, x_14, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = l_Lean_Expr_fvarId_x21(x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_3, x_17);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(x_4, x_5, x_15, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
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
x_22 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 0;
x_25 = lean_box(0);
lean_inc(x_7);
x_26 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_24, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_2);
x_30 = 0;
x_31 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_23, x_30, x_27, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
x_33 = 0;
x_34 = lean_box(0);
lean_inc(x_7);
x_35 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_33, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_5);
x_38 = l_Lean_Elab_Term_mkFreshBinderName(x_5, x_6, x_7, x_8, x_9, x_10, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed), 13, 5);
lean_closure_set(x_41, 0, x_3);
lean_closure_set(x_41, 1, x_32);
lean_closure_set(x_41, 2, x_4);
lean_closure_set(x_41, 3, x_1);
lean_closure_set(x_41, 4, x_2);
x_42 = 0;
x_43 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_39, x_42, x_36, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
return x_43;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected match type");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = x_3 < x_2;
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_uget(x_1, x_3);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 7)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_box(0);
x_32 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_elabTermEnsuringType(x_21, x_30, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_expr_instantiate1(x_29, x_34);
lean_dec(x_29);
x_37 = lean_array_push(x_24, x_34);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_4);
x_12 = x_38;
x_13 = x_35;
goto block_18;
}
else
{
uint8_t x_39; 
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_26);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_21);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3;
x_45 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_56 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 7)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_box(0);
x_63 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l_Lean_Elab_Term_elabTermEnsuringType(x_21, x_61, x_63, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_expr_instantiate1(x_60, x_65);
lean_dec(x_60);
x_68 = lean_array_push(x_55, x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_12 = x_70;
x_13 = x_66;
goto block_18;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_60);
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_73 = x_64;
} else {
 lean_dec_ref(x_64);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_21);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
lean_dec(x_56);
x_76 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3;
x_77 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_55);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_82 = lean_ctor_get(x_56, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_84 = x_56;
} else {
 lean_dec_ref(x_56);
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
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_11 = x_13;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = l_Array_empty___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1(x_1, x_13, x_14, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_finalizePatternDecls_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_finalizePatternDecls_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 3);
x_11 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_10, x_4, x_5, x_6, x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 3, x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_1, 3, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_22 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_20, x_4, x_5, x_6, x_7, x_8);
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
x_26 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_29, x_4, x_5, x_6, x_7, x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_30, x_4, x_5, x_6, x_7, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_ctor_set(x_1, 4, x_36);
lean_ctor_set(x_1, 3, x_32);
lean_ctor_set(x_34, 0, x_1);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
lean_ctor_set(x_1, 4, x_37);
lean_ctor_set(x_1, 3, x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get(x_1, 3);
x_44 = lean_ctor_get(x_1, 4);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_46 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_43, x_4, x_5, x_6, x_7, x_8);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_44, x_4, x_5, x_6, x_7, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_45);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: mvarId: ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fvar: ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = x_3 < x_2;
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_87; lean_object* x_88; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_mkMVar(x_22);
x_25 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_107 = lean_st_ref_get(x_10, x_27);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 3);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_ctor_get_uint8(x_109, sizeof(void*)*1);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = 0;
x_87 = x_112;
x_88 = x_111;
goto block_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_115 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_114, x_5, x_6, x_7, x_8, x_9, x_10, x_113);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unbox(x_116);
lean_dec(x_116);
x_87 = x_118;
x_88 = x_117;
goto block_106;
}
block_86:
{
if (lean_obj_tag(x_26) == 2)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_23);
x_30 = l_Lean_mkFVar(x_23);
lean_inc(x_30);
lean_inc(x_29);
x_71 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_29, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_get(x_10, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = 0;
x_31 = x_78;
x_32 = x_77;
goto block_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
x_80 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_81 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_31 = x_84;
x_32 = x_83;
goto block_70;
}
block_70:
{
if (x_31 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_7);
x_33 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_push(x_4, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_12 = x_40;
x_13 = x_38;
goto block_18;
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = l_Lean_mkMVar(x_29);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_30);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_56 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_55, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_7);
x_58 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_push(x_4, x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_12 = x_65;
x_13 = x_63;
goto block_18;
}
else
{
uint8_t x_66; 
lean_dec(x_7);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
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
lean_object* x_85; 
lean_dec(x_26);
lean_dec(x_23);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_4);
x_12 = x_85;
x_13 = x_28;
goto block_18;
}
}
block_106:
{
if (x_87 == 0)
{
lean_dec(x_22);
x_28 = x_88;
goto block_86;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_89, 0, x_22);
x_90 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4;
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_26);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_26);
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_inc(x_23);
x_98 = l_Lean_mkFVar(x_23);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_104 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_103, x_102, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_28 = x_105;
goto block_86;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_21, 0);
lean_inc(x_119);
lean_dec(x_21);
lean_inc(x_7);
x_120 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_119, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_121, x_5, x_6, x_7, x_8, x_9, x_10, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_array_push(x_4, x_124);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_12 = x_127;
x_13 = x_125;
goto block_18;
}
else
{
uint8_t x_128; 
lean_dec(x_7);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_120);
if (x_128 == 0)
{
return x_120;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_120, 0);
x_130 = lean_ctor_get(x_120, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_120);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_11 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_empty___closed__1;
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_finalizePatternDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_State_found___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_NameSet_contains(x_13, x_1);
lean_dec(x_13);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_NameSet_contains(x_18, x_1);
lean_dec(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_box(0);
x_16 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_14, x_1, x_15);
lean_ctor_set(x_11, 0, x_16);
x_17 = lean_st_ref_set(x_2, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
x_24 = lean_ctor_get(x_11, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_22, x_1, x_25);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
x_28 = lean_st_ref_set(x_2, x_27, x_12);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_indentExpr(x_1);
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_metavar_ctx_get_expr_assignment(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_metavar_ctx_get_expr_assignment(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_name_mk_numeral(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_15);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_name_mk_numeral(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_32, x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_take(x_1, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 4, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_42);
x_45 = lean_st_ref_set(x_1, x_44, x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg___boxed), 2, 0);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_13);
x_30 = l_Lean_Meta_inferTypeRef;
x_31 = lean_st_ref_get(x_30, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_32, x_1, x_5, x_6, x_29, x_8, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_35 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_36 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_35, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_MetavarContext_assignExpr(x_15, x_1, x_2);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_7, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_27 = l_Lean_MetavarContext_assignExpr(x_24, x_1, x_2);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_st_ref_set(x_7, x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_LocalDecl_type(x_7);
lean_dec(x_7);
x_9 = l_Lean_Expr_occurs(x_1, x_8);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Expr_mvarId_x21(x_1);
x_11 = lean_st_ref_get(x_2, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_10);
x_13 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_19 = l_Lean_Meta_inferType___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
x_22 = l_Lean_mkFVar(x_17);
x_23 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__4(x_10, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_mkFreshBinderName(x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = 0;
lean_inc(x_17);
x_30 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
x_31 = lean_st_ref_take(x_2, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_32, 2);
x_37 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5(x_1, x_35, x_28);
lean_dec(x_1);
x_38 = lean_box(0);
lean_inc(x_17);
x_39 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_36, x_17, x_38);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_array_push(x_35, x_30);
lean_ctor_set(x_32, 2, x_39);
lean_ctor_set(x_32, 1, x_40);
x_41 = lean_st_ref_set(x_2, x_32, x_33);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_17);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
lean_dec(x_37);
x_49 = l_Array_insertAt___rarg(x_35, x_48, x_30);
lean_dec(x_48);
lean_ctor_set(x_32, 2, x_39);
lean_ctor_set(x_32, 1, x_49);
x_50 = lean_st_ref_set(x_2, x_32, x_33);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_17);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_17);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_32, 0);
x_58 = lean_ctor_get(x_32, 1);
x_59 = lean_ctor_get(x_32, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_32);
x_60 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5(x_1, x_58, x_28);
lean_dec(x_1);
x_61 = lean_box(0);
lean_inc(x_17);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_59, x_17, x_61);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_array_push(x_58, x_30);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_62);
x_65 = lean_st_ref_set(x_2, x_64, x_33);
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
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_17);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
lean_dec(x_60);
x_71 = l_Array_insertAt___rarg(x_58, x_70, x_30);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_62);
x_73 = lean_st_ref_set(x_2, x_72, x_33);
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
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_17);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_19);
if (x_78 == 0)
{
return x_19;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_19, 0);
x_80 = lean_ctor_get(x_19, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_13);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_13, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_14, 0);
lean_inc(x_84);
lean_dec(x_14);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_13, 0, x_85);
return x_13;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_13, 1);
lean_inc(x_86);
lean_dec(x_13);
x_87 = lean_ctor_get(x_14, 0);
lean_inc(x_87);
lean_dec(x_14);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ToDepElimPattern_main_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ToDepElimPattern_main_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ToDepElimPattern_main_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ToDepElimPattern_main_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ToDepElimPattern_main_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_13);
x_30 = l_Lean_Meta_whnfRef;
x_31 = lean_st_ref_get(x_30, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_32, x_1, x_5, x_6, x_29, x_8, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_35 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_36 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_35, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_ToDepElimPattern_main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_LocalDecl_fvarId(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_ToDepElimPattern_main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_free_object(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Elab_Term_ToDepElimPattern_main(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_38);
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
lean_dec(x_35);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_49 = x_34;
} else {
 lean_dec_ref(x_34);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_LocalDecl_fvarId(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc(x_2);
x_15 = l_Array_extract___rarg(x_2, x_14, x_13);
x_16 = lean_array_get_size(x_2);
x_17 = l_Array_extract___rarg(x_2, x_13, x_16);
x_18 = x_17;
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2), 10, 2);
lean_closure_set(x_19, 0, x_14);
lean_closure_set(x_19, 1, x_18);
x_20 = x_19;
x_21 = lean_apply_8(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
x_27 = l_Array_toList___rarg(x_24);
lean_dec(x_24);
x_28 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
x_33 = l_Array_toList___rarg(x_29);
lean_dec(x_29);
x_34 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of auxiliary declaration 'namedPattern'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_77; 
x_77 = l_Lean_Elab_Term_inaccessible_x3f(x_1);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = l_Lean_Expr_arrayLit_x3f(x_1);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_80 = lean_unsigned_to_nat(3u);
x_81 = l_Lean_Expr_isAppOfArity___main(x_1, x_79, x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Expr_isNatLit(x_1);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Expr_isStringLit(x_1);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = l_Lean_Expr_isCharLit(x_1);
x_10 = x_84;
goto block_76;
}
else
{
uint8_t x_85; 
x_85 = 1;
x_10 = x_85;
goto block_76;
}
}
else
{
uint8_t x_86; 
x_86 = 1;
x_10 = x_86;
goto block_76;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_87);
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_sub(x_88, x_89);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_sub(x_90, x_91);
lean_dec(x_90);
x_93 = l_Lean_Expr_getRevArg_x21___main(x_1, x_92);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_94 = l_Lean_Elab_Term_ToDepElimPattern_main(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_nat_sub(x_88, x_91);
lean_dec(x_88);
x_99 = lean_nat_sub(x_98, x_91);
lean_dec(x_98);
x_100 = l_Lean_Expr_getRevArg_x21___main(x_1, x_99);
lean_dec(x_1);
if (lean_obj_tag(x_100) == 1)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_94, 0, x_102);
return x_94;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_100);
lean_free_object(x_94);
lean_dec(x_96);
x_103 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
x_104 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_94, 0);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_94);
x_107 = lean_nat_sub(x_88, x_91);
lean_dec(x_88);
x_108 = lean_nat_sub(x_107, x_91);
lean_dec(x_107);
x_109 = l_Lean_Expr_getRevArg_x21___main(x_1, x_108);
lean_dec(x_1);
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_109);
lean_dec(x_105);
x_113 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
x_114 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_106);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_88);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_94);
if (x_115 == 0)
{
return x_94;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_94, 0);
x_117 = lean_ctor_get(x_94, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_94);
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
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_1);
x_119 = lean_ctor_get(x_78, 0);
lean_inc(x_119);
lean_dec(x_78);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_122, 0, x_125);
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_120);
x_130 = !lean_is_exclusive(x_122);
if (x_130 == 0)
{
return x_122;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_122, 0);
x_132 = lean_ctor_get(x_122, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_122);
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
lean_object* x_134; 
lean_dec(x_1);
x_134 = lean_ctor_get(x_77, 0);
lean_inc(x_134);
lean_dec(x_77);
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_st_ref_get(x_2, x_9);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
x_141 = lean_array_get_size(x_140);
x_142 = lean_unsigned_to_nat(0u);
x_143 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6(x_135, x_138, x_140, x_141, x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_138);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_136, 0, x_144);
return x_136;
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_free_object(x_136);
x_145 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_139);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_148);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_149, 0);
lean_dec(x_151);
x_152 = l_Lean_Expr_fvarId_x21(x_134);
lean_dec(x_134);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_149, 0, x_153);
return x_149;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_dec(x_149);
x_155 = l_Lean_Expr_fvarId_x21(x_134);
lean_dec(x_134);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_145);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_145, 0);
lean_dec(x_159);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_134);
lean_ctor_set(x_145, 0, x_160);
return x_145;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_145, 1);
lean_inc(x_161);
lean_dec(x_145);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_134);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_164 = lean_ctor_get(x_136, 0);
x_165 = lean_ctor_get(x_136, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_136);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
x_167 = lean_array_get_size(x_166);
x_168 = lean_unsigned_to_nat(0u);
x_169 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6(x_135, x_164, x_166, x_167, x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_164);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_134);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_165);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_175);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_179 = l_Lean_Expr_fvarId_x21(x_134);
lean_dec(x_134);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_183 = x_172;
} else {
 lean_dec_ref(x_172);
 x_183 = lean_box(0);
}
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_134);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_134);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_9);
return x_187;
}
}
block_76:
{
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isFVar(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isMVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_13 = l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_51; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_51 = lean_expr_eqv(x_14, x_1);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = 1;
x_16 = x_52;
goto block_50;
}
else
{
uint8_t x_53; 
x_53 = 0;
x_16 = x_53;
goto block_50;
}
block_50:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_8, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_find(x_23, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_19);
x_25 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
lean_inc(x_1);
x_34 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_31, x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_ctor_get(x_27, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 4);
lean_inc(x_37);
x_38 = lean_nat_add(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_19);
x_40 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(x_27, x_34, x_19, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_26);
lean_dec(x_19);
x_47 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_17);
x_48 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
else
{
lean_dec(x_1);
x_1 = x_14;
x_9 = x_15;
goto _start;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
x_58 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = l_Lean_Expr_fvarId_x21(x_1);
x_60 = lean_st_ref_get(x_2, x_9);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_array_get_size(x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_59, x_61, x_63, x_64, x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_61);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_59);
x_67 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(x_59, x_1, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_1);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
return x_75;
}
}
}
}
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDepElimPatterns_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_ToDepElimPattern_main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_16, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_9 = x_20;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_LocalDecl_fvarId(x_7);
lean_dec(x_7);
x_9 = lean_local_ctx_erase(x_4, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_LocalContext_addDecl(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = x_2;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1), 10, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_NameSet_empty;
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_st_mk_ref(x_15, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = x_13;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_20 = lean_apply_8(x_19, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_17, x_22);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = x_26;
x_28 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed), 9, 2);
lean_closure_set(x_28, 0, x_12);
lean_closure_set(x_28, 1, x_27);
x_29 = x_28;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = lean_apply_7(x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_6, 1);
x_35 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_31, x_31, x_12, x_34);
x_36 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_31, x_31, x_12, x_35);
lean_ctor_set(x_6, 1, x_36);
x_37 = lean_apply_9(x_3, x_31, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get(x_6, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_41 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_31, x_31, x_12, x_39);
x_42 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_31, x_31, x_12, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_apply_9(x_3, x_31, x_21, x_4, x_5, x_43, x_7, x_8, x_9, x_32);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDepElimPatterns___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_16, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_9 = x_20;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Array_toList___rarg(x_4);
x_14 = l_Array_toList___rarg(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_apply_9(x_2, x_15, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___boxed), 9, 2);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_withSynthesize___rarg(x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_8);
x_19 = l_Lean_Elab_Term_finalizePatternDecls(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = x_17;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed), 9, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_22);
x_25 = x_24;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = lean_apply_7(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1___boxed), 12, 3);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_5);
lean_closure_set(x_29, 2, x_18);
x_30 = l_Lean_Elab_Term_withDepElimPatterns___rarg(x_20, x_27, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_String_splitAux___main___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rhs: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_get(x_9, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = 0;
x_11 = x_33;
x_12 = x_32;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_2);
x_35 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_11 = x_38;
x_12 = x_37;
goto block_27;
}
block_27:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_3);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = lean_box(0);
x_15 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_elabTermEnsuringType(x_12, x_13, x_15, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = l_List_redLength___main___rarg(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
x_22 = l_List_toArrayAux___main___rarg(x_19, x_21);
x_23 = x_22;
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_24, x_23);
x_26 = x_25;
x_27 = l_Array_isEmpty___rarg(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_7);
x_28 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_26, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_3, x_2, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_36 = l_Lean_mkSimpleThunk(x_17);
x_37 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_3, x_2, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2), 11, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
x_15 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(x_12, x_4, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("patternVars: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatchAltView___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_12);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
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
x_38 = lean_st_ref_get(x_8, x_17);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = 0;
x_20 = x_43;
x_21 = x_42;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_46 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_20 = x_49;
x_21 = x_48;
goto block_37;
}
block_37:
{
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_2);
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_18, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = l_Array_toList___rarg(x_18);
x_26 = l_List_map___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_25);
x_27 = l_Lean_MessageData_ofList(x_26);
lean_dec(x_26);
x_28 = l_Lean_Elab_Term_elabMatchAltView___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_33 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_32, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_35, 0, x_19);
lean_closure_set(x_35, 1, x_32);
lean_closure_set(x_35, 2, x_2);
x_36 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_18, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
return x_36;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
x_56 = lean_ctor_get(x_7, 2);
x_57 = lean_ctor_get(x_7, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_58 = l_Lean_replaceRef(x_10, x_57);
lean_dec(x_10);
x_59 = l_Lean_replaceRef(x_58, x_57);
lean_dec(x_57);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_59);
lean_inc(x_8);
lean_inc(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_60, x_8, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_84 = lean_st_ref_get(x_8, x_63);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 3);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = 0;
x_66 = x_89;
x_67 = x_88;
goto block_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_92 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_91, x_3, x_4, x_5, x_6, x_60, x_8, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_unbox(x_93);
lean_dec(x_93);
x_66 = x_95;
x_67 = x_94;
goto block_83;
}
block_83:
{
if (x_66 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_69 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_69, 0, x_65);
lean_closure_set(x_69, 1, x_68);
lean_closure_set(x_69, 2, x_2);
x_70 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_64, x_69, x_3, x_4, x_5, x_6, x_60, x_8, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = l_Array_toList___rarg(x_64);
x_72 = l_List_map___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_71);
x_73 = l_Lean_MessageData_ofList(x_72);
lean_dec(x_72);
x_74 = l_Lean_Elab_Term_elabMatchAltView___closed__2;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_79 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_78, x_77, x_3, x_4, x_5, x_6, x_60, x_8, x_67);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_81, 0, x_65);
lean_closure_set(x_81, 1, x_78);
lean_closure_set(x_81, 2, x_2);
x_82 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_64, x_81, x_3, x_4, x_5, x_6, x_60, x_8, x_80);
return x_82;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_61, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_61, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_98 = x_61;
} else {
 lean_dec_ref(x_61);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabMatchAltView___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_mkMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Match_mkMatcher(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_mkMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_mkMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = l_Nat_repr(x_7);
x_9 = l_Array_HasRepr___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_String_splitAux___main___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_5);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_14, x_16);
lean_dec(x_14);
x_18 = l_Nat_repr(x_17);
x_19 = l_Array_HasRepr___rarg___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_String_splitAux___main___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(lean_object* x_1) {
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
x_6 = l_Lean_stringToMessageData(x_4);
lean_dec(x_4);
x_7 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(x_5);
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
x_10 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unused alternatives: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_List_isEmpty___rarg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_10);
x_13 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(x_12);
x_14 = l_Lean_MessageData_ofList(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing cases:\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_counterExamplesToMessageData(x_9);
x_12 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_reportMatcherResultErrors(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_3, x_2, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_elabMatchAltView(x_18, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_2, x_24);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_ctor_get(x_9, 1);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___rarg), 1, 0);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_141 = lean_st_ref_get(x_10, x_15);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_9, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_9, 2);
lean_inc(x_149);
x_150 = lean_st_ref_get(x_10, x_147);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_144);
x_154 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_154, 0, x_144);
x_155 = x_154;
x_156 = lean_environment_main_module(x_144);
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_146);
lean_ctor_set(x_157, 3, x_148);
lean_ctor_set(x_157, 4, x_149);
x_158 = l_Lean_Elab_Term_expandMacrosInPatterns(x_18, x_157, x_153);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_take(x_10, x_152);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = !lean_is_exclusive(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_162, 1);
lean_dec(x_165);
lean_ctor_set(x_162, 1, x_160);
x_166 = lean_st_ref_set(x_10, x_162, x_163);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_19 = x_159;
x_20 = x_167;
goto block_140;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_162, 0);
x_169 = lean_ctor_get(x_162, 2);
x_170 = lean_ctor_get(x_162, 3);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_162);
x_171 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_160);
lean_ctor_set(x_171, 2, x_169);
lean_ctor_set(x_171, 3, x_170);
x_172 = lean_st_ref_set(x_10, x_171, x_163);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_19 = x_159;
x_20 = x_173;
goto block_140;
}
}
else
{
lean_object* x_174; 
lean_dec(x_17);
lean_dec(x_16);
x_174 = lean_ctor_get(x_158, 0);
lean_inc(x_174);
lean_dec(x_158);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_175, x_178, x_5, x_6, x_7, x_8, x_9, x_10, x_152);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_175);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
return x_179;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_179);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
else
{
lean_object* x_184; uint8_t x_185; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_184 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___rarg(x_152);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
return x_184;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_184);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
block_140:
{
lean_object* x_21; uint8_t x_117; lean_object* x_118; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_st_ref_get(x_10, x_20);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 3);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_ctor_get_uint8(x_130, sizeof(void*)*1);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = 0;
x_117 = x_133;
x_118 = x_132;
goto block_127;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
x_135 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_136 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_135, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_unbox(x_137);
lean_dec(x_137);
x_117 = x_139;
x_118 = x_138;
goto block_127;
}
block_116:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = x_19;
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_24 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1), 10, 3);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_22);
x_25 = x_24;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = lean_apply_7(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_29, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_synthesizeUsingDefault(x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = x_27;
lean_inc(x_35);
x_36 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(x_23, x_35);
x_37 = x_36;
x_38 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3(x_23, x_35);
x_39 = x_38;
x_40 = lean_array_get_size(x_16);
x_41 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1;
lean_inc(x_5);
x_42 = l_Lean_Elab_Term_mkAuxName(x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Array_toList___rarg(x_39);
lean_dec(x_39);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_40);
lean_inc(x_17);
x_46 = l_Lean_Meta_Match_mkMatcher(x_43, x_17, x_40, x_45, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_40);
x_50 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_51 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_17, x_49, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_5);
lean_inc(x_47);
x_54 = l_Lean_Elab_Term_reportMatcherResultErrors(x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
lean_dec(x_47);
x_58 = l_Lean_mkApp(x_57, x_52);
x_59 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_16, x_16, x_23, x_58);
lean_dec(x_16);
x_60 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_37, x_37, x_23, x_59);
lean_dec(x_37);
x_76 = lean_st_ref_get(x_10, x_55);
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
x_61 = x_81;
x_62 = x_80;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_84 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_83, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_61 = x_87;
x_62 = x_86;
goto block_75;
}
block_75:
{
if (x_61 == 0)
{
lean_object* x_63; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_56)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_56;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_56);
lean_inc(x_60);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_60);
x_65 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_70 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_69, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_60);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_54);
if (x_88 == 0)
{
return x_54;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_54, 0);
x_90 = lean_ctor_get(x_54, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_54);
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
lean_dec(x_47);
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_92 = !lean_is_exclusive(x_51);
if (x_92 == 0)
{
return x_51;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_51, 0);
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_51);
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
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
return x_46;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_46, 0);
x_98 = lean_ctor_get(x_46, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_46);
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
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_100 = !lean_is_exclusive(x_42);
if (x_100 == 0)
{
return x_42;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_42, 0);
x_102 = lean_ctor_get(x_42, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_42);
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
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_33);
if (x_104 == 0)
{
return x_33;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_33, 0);
x_106 = lean_ctor_get(x_33, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_33);
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
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_108 = !lean_is_exclusive(x_31);
if (x_108 == 0)
{
return x_31;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_31, 0);
x_110 = lean_ctor_get(x_31, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_31);
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
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_112 = !lean_is_exclusive(x_26);
if (x_112 == 0)
{
return x_26;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_26, 0);
x_114 = lean_ctor_get(x_26, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_26);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
block_127:
{
if (x_117 == 0)
{
x_21 = x_118;
goto block_116;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc(x_17);
x_119 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_119, 0, x_17);
x_120 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__6;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_125 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_124, x_123, x_5, x_6, x_7, x_8, x_9, x_10, x_118);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_21 = x_126;
goto block_116;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_189 = !lean_is_exclusive(x_12);
if (x_189 == 0)
{
return x_12;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_12, 0);
x_191 = lean_ctor_get(x_12, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_12);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getSepArgs(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_setArg(x_1, x_19, x_2);
x_21 = lean_array_push(x_3, x_20);
lean_inc(x_14);
lean_inc(x_12);
x_22 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(x_4, x_5, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getCurrMacroScope(x_12, x_13, x_14, x_15, x_16, x_17, x_24);
lean_dec(x_14);
lean_dec(x_12);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_getMainModule___rarg(x_17, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__1;
lean_inc(x_6);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_addMacroScope(x_30, x_7, x_26);
lean_inc(x_6);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_8);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_9);
x_37 = lean_array_push(x_33, x_36);
x_38 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_array_push(x_39, x_38);
x_41 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__19;
lean_inc(x_6);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_40, x_42);
x_44 = lean_array_push(x_43, x_10);
x_45 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_33, x_46);
x_48 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_34, x_49);
x_51 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__15;
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_33, x_52);
x_54 = l_Lean_nullKind___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_50, x_55);
x_57 = lean_array_push(x_56, x_23);
x_58 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_28, 0, x_59);
return x_28;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_60 = lean_ctor_get(x_28, 0);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_28);
x_62 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__1;
lean_inc(x_6);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_6);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Array_empty___closed__1;
x_65 = lean_array_push(x_64, x_63);
x_66 = l_Lean_addMacroScope(x_60, x_7, x_26);
lean_inc(x_6);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_8);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_9);
x_68 = lean_array_push(x_64, x_67);
x_69 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_array_push(x_70, x_69);
x_72 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__19;
lean_inc(x_6);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_71, x_73);
x_75 = lean_array_push(x_74, x_10);
x_76 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_64, x_77);
x_79 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_65, x_80);
x_82 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__15;
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_64, x_83);
x_85 = l_Lean_nullKind___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_81, x_86);
x_88 = lean_array_push(x_87, x_23);
x_89 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_61);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_92 = !lean_is_exclusive(x_22);
if (x_92 == 0)
{
return x_22;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_22, 0);
x_94 = lean_ctor_get(x_22, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_22);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected internal auxiliary discriminant name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
x_11 = l_List_reprAux___main___rarg___closed__1;
x_12 = l_Lean_mkAtomFrom(x_1, x_11);
x_13 = l_Lean_mkSepStx(x_3, x_12);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_setArg(x_1, x_14, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_17, x_19);
lean_inc(x_6);
lean_inc(x_20);
x_21 = l_Lean_Elab_Term_isLocalIdent_x3f(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_9, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_nat_add(x_28, x_19);
lean_ctor_set(x_25, 1, x_29);
x_30 = lean_st_ref_set(x_9, x_25, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_33 = lean_ctor_get(x_4, 7);
lean_dec(x_33);
lean_ctor_set(x_4, 7, x_28);
x_34 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
x_41 = l_Lean_addMacroScope(x_38, x_40, x_35);
x_42 = lean_box(0);
x_43 = l_Lean_SourceInfo_inhabited___closed__1;
x_44 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
x_46 = l_Lean_Syntax_getId(x_45);
x_47 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_45);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_48 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_6);
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
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
x_55 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_45, x_3, x_1, x_18, x_43, x_40, x_44, x_42, x_20, x_54, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
x_58 = lean_ctor_get(x_4, 2);
x_59 = lean_ctor_get(x_4, 3);
x_60 = lean_ctor_get(x_4, 4);
x_61 = lean_ctor_get(x_4, 5);
x_62 = lean_ctor_get(x_4, 6);
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_65 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_59);
lean_ctor_set(x_65, 4, x_60);
lean_ctor_set(x_65, 5, x_61);
lean_ctor_set(x_65, 6, x_62);
lean_ctor_set(x_65, 7, x_28);
lean_ctor_set_uint8(x_65, sizeof(void*)*8, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*8 + 1, x_64);
x_66 = l_Lean_Elab_Term_getCurrMacroScope(x_65, x_5, x_6, x_7, x_8, x_9, x_31);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
x_73 = l_Lean_addMacroScope(x_70, x_72, x_67);
x_74 = lean_box(0);
x_75 = l_Lean_SourceInfo_inhabited___closed__1;
x_76 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_74);
x_78 = l_Lean_Syntax_getId(x_77);
x_79 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_77);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_80 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_81 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_80, x_65, x_5, x_6, x_7, x_8, x_9, x_71);
lean_dec(x_6);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_box(0);
x_87 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_77, x_3, x_1, x_18, x_75, x_72, x_76, x_74, x_20, x_86, x_65, x_5, x_6, x_7, x_8, x_9, x_71);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_88 = lean_ctor_get(x_25, 0);
x_89 = lean_ctor_get(x_25, 1);
x_90 = lean_ctor_get(x_25, 2);
x_91 = lean_ctor_get(x_25, 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_25);
x_92 = lean_nat_add(x_89, x_19);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
x_94 = lean_st_ref_set(x_9, x_93, x_26);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_4, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_4, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_4, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_4, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_4, 5);
lean_inc(x_101);
x_102 = lean_ctor_get(x_4, 6);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_104 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 x_105 = x_4;
} else {
 lean_dec_ref(x_4);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 8, 2);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_97);
lean_ctor_set(x_106, 2, x_98);
lean_ctor_set(x_106, 3, x_99);
lean_ctor_set(x_106, 4, x_100);
lean_ctor_set(x_106, 5, x_101);
lean_ctor_set(x_106, 6, x_102);
lean_ctor_set(x_106, 7, x_89);
lean_ctor_set_uint8(x_106, sizeof(void*)*8, x_103);
lean_ctor_set_uint8(x_106, sizeof(void*)*8 + 1, x_104);
x_107 = l_Lean_Elab_Term_getCurrMacroScope(x_106, x_5, x_6, x_7, x_8, x_9, x_95);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
x_114 = l_Lean_addMacroScope(x_111, x_113, x_108);
x_115 = lean_box(0);
x_116 = l_Lean_SourceInfo_inhabited___closed__1;
x_117 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_118 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_114);
lean_ctor_set(x_118, 3, x_115);
x_119 = l_Lean_Syntax_getId(x_118);
x_120 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_118);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_121 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_122 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_121, x_106, x_5, x_6, x_7, x_8, x_9, x_112);
lean_dec(x_6);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_box(0);
x_128 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_118, x_3, x_1, x_18, x_116, x_113, x_117, x_115, x_20, x_127, x_106, x_5, x_6, x_7, x_8, x_9, x_112);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_22);
lean_dec(x_20);
x_129 = lean_ctor_get(x_21, 1);
lean_inc(x_129);
lean_dec(x_21);
x_130 = lean_array_push(x_3, x_17);
x_2 = x_18;
x_3 = x_130;
x_10 = x_129;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_4, x_3);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_4);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_16, x_17);
lean_dec(x_16);
lean_inc(x_7);
x_19 = l_Lean_Elab_Term_isLocalIdent_x3f(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_4 = x_30;
x_11 = x_29;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_34 = lean_array_get_size(x_14);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_36 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(x_1, x_14, x_34, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = 1;
x_15 = x_40;
x_16 = x_39;
goto block_33;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = 0;
x_15 = x_42;
x_16 = x_41;
goto block_33;
}
block_33:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
x_18 = l_Array_empty___closed__1;
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(x_1, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
return x_32;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discr ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = x_3 < x_2;
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_21, x_22);
lean_inc(x_7);
x_24 = l_Lean_Elab_Term_isLocalIdent_x3f(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3;
x_28 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_21, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_21);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_35 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_67 = lean_st_ref_get(x_10, x_37);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = 0;
x_38 = x_72;
x_39 = x_71;
goto block_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_75 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_74, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_38 = x_78;
x_39 = x_77;
goto block_66;
}
block_66:
{
if (x_38 == 0)
{
lean_object* x_40; 
lean_dec(x_34);
x_40 = l_Lean_Elab_Term_tryPostponeIfMVar(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_12 = x_42;
x_13 = x_41;
goto block_18;
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_34);
x_48 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_36);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_36);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_57 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_56, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Elab_Term_tryPostponeIfMVar(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_12 = x_61;
x_13 = x_60;
goto block_18;
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_35);
if (x_79 == 0)
{
return x_35;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_35, 0);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_35);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_11 = x_13;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_8, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_14 = x_13;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore___spec__1(x_15, x_14);
x_17 = x_16;
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(x_1);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(x_17, x_18, x_20, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_20);
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
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__7___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__8___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__9___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__10___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__11___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__12___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__13___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__14___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__15___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__16___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__17___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__17___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__18___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__18___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__19___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__20___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__21___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__22___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__22___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__23___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__23___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__24___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__24(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__24___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__25___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__25(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__25___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_match__26___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_match__26(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_match__26___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match expected type should not be provided when discriminants with equality proofs are used");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatch___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatch___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
lean_inc(x_1);
x_60 = l_Lean_Syntax_isOfKind(x_1, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_10 = x_61;
goto block_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = l_Lean_Syntax_getArgs(x_1);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
x_64 = lean_unsigned_to_nat(5u);
x_65 = lean_nat_dec_eq(x_63, x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
x_10 = x_66;
goto block_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = l_Lean_Syntax_getArg(x_1, x_67);
x_69 = l_Lean_nullKind___closed__2;
lean_inc(x_68);
x_70 = l_Lean_Syntax_isOfKind(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
x_71 = lean_box(0);
x_10 = x_71;
goto block_58;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_Syntax_getArgs(x_68);
x_73 = lean_array_get_size(x_72);
lean_dec(x_72);
x_74 = lean_nat_dec_eq(x_73, x_67);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_68);
x_75 = lean_box(0);
x_10 = x_75;
goto block_58;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Syntax_getArg(x_68, x_76);
lean_dec(x_68);
x_78 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
lean_inc(x_77);
x_79 = l_Lean_Syntax_isOfKind(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_77);
x_80 = lean_box(0);
x_10 = x_80;
goto block_58;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = l_Lean_Syntax_getArgs(x_77);
x_82 = lean_array_get_size(x_81);
lean_dec(x_81);
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_dec_eq(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_77);
x_85 = lean_box(0);
x_10 = x_85;
goto block_58;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = l_Lean_Syntax_getArg(x_77, x_76);
lean_inc(x_86);
x_87 = l_Lean_Syntax_isOfKind(x_86, x_69);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_86);
lean_dec(x_77);
x_88 = lean_box(0);
x_10 = x_88;
goto block_58;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = l_Lean_Syntax_getArgs(x_86);
lean_dec(x_86);
x_90 = lean_array_get_size(x_89);
lean_dec(x_89);
x_91 = lean_nat_dec_eq(x_90, x_76);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_77);
x_92 = lean_box(0);
x_10 = x_92;
goto block_58;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_275; 
x_93 = l_Lean_Syntax_getArg(x_77, x_67);
lean_dec(x_77);
x_94 = l_Lean_Syntax_getArg(x_1, x_83);
lean_inc(x_94);
x_275 = l_Lean_Syntax_isOfKind(x_94, x_69);
if (x_275 == 0)
{
lean_object* x_276; 
x_276 = lean_box(0);
x_95 = x_276;
goto block_274;
}
else
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_277 = l_Lean_Syntax_getArgs(x_94);
x_278 = lean_array_get_size(x_277);
lean_dec(x_277);
x_279 = lean_nat_dec_eq(x_278, x_76);
lean_dec(x_278);
if (x_279 == 0)
{
lean_object* x_280; 
x_280 = lean_box(0);
x_95 = x_280;
goto block_274;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_94);
x_281 = lean_unsigned_to_nat(4u);
x_282 = l_Lean_Syntax_getArg(x_1, x_281);
x_283 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
lean_inc(x_282);
x_284 = l_Lean_Syntax_isOfKind(x_282, x_283);
if (x_284 == 0)
{
lean_object* x_285; 
lean_dec(x_282);
lean_dec(x_93);
x_285 = lean_box(0);
x_10 = x_285;
goto block_58;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = l_Lean_Syntax_getArgs(x_282);
x_287 = lean_array_get_size(x_286);
lean_dec(x_286);
x_288 = lean_nat_dec_eq(x_287, x_83);
lean_dec(x_287);
if (x_288 == 0)
{
lean_object* x_289; 
lean_dec(x_282);
lean_dec(x_93);
x_289 = lean_box(0);
x_10 = x_289;
goto block_58;
}
else
{
lean_object* x_290; uint8_t x_291; 
x_290 = l_Lean_Syntax_getArg(x_282, x_76);
lean_inc(x_290);
x_291 = l_Lean_Syntax_isOfKind(x_290, x_69);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec(x_290);
lean_dec(x_282);
lean_dec(x_93);
x_292 = lean_box(0);
x_10 = x_292;
goto block_58;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = l_Lean_Syntax_getArgs(x_290);
lean_dec(x_290);
x_294 = lean_array_get_size(x_293);
lean_dec(x_293);
x_295 = lean_nat_dec_eq(x_294, x_76);
if (x_295 == 0)
{
uint8_t x_296; 
x_296 = lean_nat_dec_eq(x_294, x_67);
lean_dec(x_294);
if (x_296 == 0)
{
lean_object* x_297; 
lean_dec(x_282);
lean_dec(x_93);
x_297 = lean_box(0);
x_10 = x_297;
goto block_58;
}
else
{
lean_object* x_298; uint8_t x_299; 
x_298 = l_Lean_Syntax_getArg(x_282, x_67);
lean_dec(x_282);
lean_inc(x_298);
x_299 = l_Lean_Syntax_isOfKind(x_298, x_69);
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec(x_298);
lean_dec(x_93);
x_300 = lean_box(0);
x_10 = x_300;
goto block_58;
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = l_Lean_Syntax_getArgs(x_298);
x_302 = lean_array_get_size(x_301);
lean_dec(x_301);
x_303 = lean_nat_dec_eq(x_302, x_67);
lean_dec(x_302);
if (x_303 == 0)
{
lean_object* x_304; 
lean_dec(x_298);
lean_dec(x_93);
x_304 = lean_box(0);
x_10 = x_304;
goto block_58;
}
else
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = l_Lean_Syntax_getArg(x_298, x_76);
lean_dec(x_298);
x_306 = l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
lean_inc(x_305);
x_307 = l_Lean_Syntax_isOfKind(x_305, x_306);
if (x_307 == 0)
{
lean_object* x_308; 
lean_dec(x_305);
lean_dec(x_93);
x_308 = lean_box(0);
x_10 = x_308;
goto block_58;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_309 = l_Lean_Syntax_getArgs(x_305);
x_310 = lean_array_get_size(x_309);
lean_dec(x_309);
x_311 = lean_unsigned_to_nat(3u);
x_312 = lean_nat_dec_eq(x_310, x_311);
lean_dec(x_310);
if (x_312 == 0)
{
lean_object* x_313; 
lean_dec(x_305);
lean_dec(x_93);
x_313 = lean_box(0);
x_10 = x_313;
goto block_58;
}
else
{
lean_object* x_314; uint8_t x_315; 
x_314 = l_Lean_Syntax_getArg(x_305, x_76);
lean_inc(x_314);
x_315 = l_Lean_Syntax_isOfKind(x_314, x_69);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_314);
lean_dec(x_305);
lean_dec(x_93);
x_316 = lean_box(0);
x_10 = x_316;
goto block_58;
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = l_Lean_Syntax_getArgs(x_314);
x_318 = lean_array_get_size(x_317);
lean_dec(x_317);
x_319 = lean_nat_dec_eq(x_318, x_67);
lean_dec(x_318);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_314);
lean_dec(x_305);
lean_dec(x_93);
x_320 = lean_box(0);
x_10 = x_320;
goto block_58;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = l_Lean_Syntax_getArg(x_314, x_76);
lean_dec(x_314);
x_322 = l_Lean_identKind___closed__2;
lean_inc(x_321);
x_323 = l_Lean_Syntax_isOfKind(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_321);
lean_dec(x_305);
lean_dec(x_93);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_324 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; uint8_t x_338; 
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_328 = l_Lean_Syntax_getArg(x_1, x_83);
x_338 = l_Lean_Syntax_isNone(x_328);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_array_get_size(x_327);
x_340 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__4(x_1, x_327, x_339, x_76);
lean_dec(x_339);
lean_dec(x_327);
x_329 = x_340;
goto block_337;
}
else
{
uint8_t x_341; 
lean_dec(x_327);
x_341 = 0;
x_329 = x_341;
goto block_337;
}
block_337:
{
if (x_329 == 0)
{
lean_object* x_330; 
lean_dec(x_328);
x_330 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_326);
lean_dec(x_1);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_dec(x_2);
lean_dec(x_1);
x_331 = l_Lean_Elab_Term_elabMatch___closed__3;
x_332 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_328, x_331, x_3, x_4, x_5, x_6, x_7, x_8, x_326);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_328);
x_333 = !lean_is_exclusive(x_332);
if (x_333 == 0)
{
return x_332;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_332);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_324, 1);
lean_inc(x_342);
lean_dec(x_324);
x_343 = lean_ctor_get(x_325, 0);
lean_inc(x_343);
lean_dec(x_325);
x_344 = !lean_is_exclusive(x_3);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_345 = lean_ctor_get(x_3, 6);
lean_inc(x_343);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_1);
lean_ctor_set(x_346, 1, x_343);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_345);
lean_ctor_set(x_3, 6, x_347);
x_348 = 1;
x_349 = l_Lean_Elab_Term_elabTerm(x_343, x_2, x_348, x_3, x_4, x_5, x_6, x_7, x_8, x_342);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; 
x_350 = lean_ctor_get(x_3, 0);
x_351 = lean_ctor_get(x_3, 1);
x_352 = lean_ctor_get(x_3, 2);
x_353 = lean_ctor_get(x_3, 3);
x_354 = lean_ctor_get(x_3, 4);
x_355 = lean_ctor_get(x_3, 5);
x_356 = lean_ctor_get(x_3, 6);
x_357 = lean_ctor_get(x_3, 7);
x_358 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_359 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_3);
lean_inc(x_343);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_1);
lean_ctor_set(x_360, 1, x_343);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_356);
x_362 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_362, 0, x_350);
lean_ctor_set(x_362, 1, x_351);
lean_ctor_set(x_362, 2, x_352);
lean_ctor_set(x_362, 3, x_353);
lean_ctor_set(x_362, 4, x_354);
lean_ctor_set(x_362, 5, x_355);
lean_ctor_set(x_362, 6, x_361);
lean_ctor_set(x_362, 7, x_357);
lean_ctor_set_uint8(x_362, sizeof(void*)*8, x_358);
lean_ctor_set_uint8(x_362, sizeof(void*)*8 + 1, x_359);
x_363 = 1;
x_364 = l_Lean_Elab_Term_elabTerm(x_343, x_2, x_363, x_362, x_4, x_5, x_6, x_7, x_8, x_342);
return x_364;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_365 = !lean_is_exclusive(x_324);
if (x_365 == 0)
{
return x_324;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_324, 0);
x_367 = lean_ctor_get(x_324, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_324);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = l_Lean_Syntax_getArg(x_305, x_83);
lean_dec(x_305);
x_370 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(x_1, x_93, x_321, x_369, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_370;
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
lean_object* x_371; uint8_t x_372; 
lean_dec(x_294);
x_371 = l_Lean_Syntax_getArg(x_282, x_67);
lean_dec(x_282);
lean_inc(x_371);
x_372 = l_Lean_Syntax_isOfKind(x_371, x_69);
if (x_372 == 0)
{
lean_object* x_373; 
lean_dec(x_371);
lean_dec(x_93);
x_373 = lean_box(0);
x_10 = x_373;
goto block_58;
}
else
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = l_Lean_Syntax_getArgs(x_371);
x_375 = lean_array_get_size(x_374);
lean_dec(x_374);
x_376 = lean_nat_dec_eq(x_375, x_67);
lean_dec(x_375);
if (x_376 == 0)
{
lean_object* x_377; 
lean_dec(x_371);
lean_dec(x_93);
x_377 = lean_box(0);
x_10 = x_377;
goto block_58;
}
else
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_378 = l_Lean_Syntax_getArg(x_371, x_76);
lean_dec(x_371);
x_379 = l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
lean_inc(x_378);
x_380 = l_Lean_Syntax_isOfKind(x_378, x_379);
if (x_380 == 0)
{
lean_object* x_381; 
lean_dec(x_378);
lean_dec(x_93);
x_381 = lean_box(0);
x_10 = x_381;
goto block_58;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_382 = l_Lean_Syntax_getArgs(x_378);
x_383 = lean_array_get_size(x_382);
lean_dec(x_382);
x_384 = lean_unsigned_to_nat(3u);
x_385 = lean_nat_dec_eq(x_383, x_384);
lean_dec(x_383);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_378);
lean_dec(x_93);
x_386 = lean_box(0);
x_10 = x_386;
goto block_58;
}
else
{
lean_object* x_387; uint8_t x_388; 
x_387 = l_Lean_Syntax_getArg(x_378, x_76);
lean_inc(x_387);
x_388 = l_Lean_Syntax_isOfKind(x_387, x_69);
if (x_388 == 0)
{
lean_object* x_389; 
lean_dec(x_387);
lean_dec(x_378);
lean_dec(x_93);
x_389 = lean_box(0);
x_10 = x_389;
goto block_58;
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_390 = l_Lean_Syntax_getArgs(x_387);
x_391 = lean_array_get_size(x_390);
lean_dec(x_390);
x_392 = lean_nat_dec_eq(x_391, x_67);
lean_dec(x_391);
if (x_392 == 0)
{
lean_object* x_393; 
lean_dec(x_387);
lean_dec(x_378);
lean_dec(x_93);
x_393 = lean_box(0);
x_10 = x_393;
goto block_58;
}
else
{
lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_394 = l_Lean_Syntax_getArg(x_387, x_76);
lean_dec(x_387);
x_395 = l_Lean_identKind___closed__2;
lean_inc(x_394);
x_396 = l_Lean_Syntax_isOfKind(x_394, x_395);
if (x_396 == 0)
{
lean_object* x_397; 
lean_dec(x_394);
lean_dec(x_378);
lean_dec(x_93);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_397 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_411; 
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_401 = l_Lean_Syntax_getArg(x_1, x_83);
x_411 = l_Lean_Syntax_isNone(x_401);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; 
x_412 = lean_array_get_size(x_400);
x_413 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__5(x_1, x_400, x_412, x_76);
lean_dec(x_412);
lean_dec(x_400);
x_402 = x_413;
goto block_410;
}
else
{
uint8_t x_414; 
lean_dec(x_400);
x_414 = 0;
x_402 = x_414;
goto block_410;
}
block_410:
{
if (x_402 == 0)
{
lean_object* x_403; 
lean_dec(x_401);
x_403 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_399);
lean_dec(x_1);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; 
lean_dec(x_2);
lean_dec(x_1);
x_404 = l_Lean_Elab_Term_elabMatch___closed__3;
x_405 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_401, x_404, x_3, x_4, x_5, x_6, x_7, x_8, x_399);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_401);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
return x_405;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_405, 0);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_405);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_415 = lean_ctor_get(x_397, 1);
lean_inc(x_415);
lean_dec(x_397);
x_416 = lean_ctor_get(x_398, 0);
lean_inc(x_416);
lean_dec(x_398);
x_417 = !lean_is_exclusive(x_3);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_3, 6);
lean_inc(x_416);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_1);
lean_ctor_set(x_419, 1, x_416);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set(x_3, 6, x_420);
x_421 = 1;
x_422 = l_Lean_Elab_Term_elabTerm(x_416, x_2, x_421, x_3, x_4, x_5, x_6, x_7, x_8, x_415);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_423 = lean_ctor_get(x_3, 0);
x_424 = lean_ctor_get(x_3, 1);
x_425 = lean_ctor_get(x_3, 2);
x_426 = lean_ctor_get(x_3, 3);
x_427 = lean_ctor_get(x_3, 4);
x_428 = lean_ctor_get(x_3, 5);
x_429 = lean_ctor_get(x_3, 6);
x_430 = lean_ctor_get(x_3, 7);
x_431 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_432 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_3);
lean_inc(x_416);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_1);
lean_ctor_set(x_433, 1, x_416);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_429);
x_435 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_435, 0, x_423);
lean_ctor_set(x_435, 1, x_424);
lean_ctor_set(x_435, 2, x_425);
lean_ctor_set(x_435, 3, x_426);
lean_ctor_set(x_435, 4, x_427);
lean_ctor_set(x_435, 5, x_428);
lean_ctor_set(x_435, 6, x_434);
lean_ctor_set(x_435, 7, x_430);
lean_ctor_set_uint8(x_435, sizeof(void*)*8, x_431);
lean_ctor_set_uint8(x_435, sizeof(void*)*8 + 1, x_432);
x_436 = 1;
x_437 = l_Lean_Elab_Term_elabTerm(x_416, x_2, x_436, x_435, x_4, x_5, x_6, x_7, x_8, x_415);
return x_437;
}
}
}
else
{
uint8_t x_438; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_438 = !lean_is_exclusive(x_397);
if (x_438 == 0)
{
return x_397;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_397, 0);
x_440 = lean_ctor_get(x_397, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_397);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = l_Lean_Syntax_getArg(x_378, x_83);
lean_dec(x_378);
x_443 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(x_1, x_93, x_394, x_442, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_443;
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
}
block_274:
{
uint8_t x_96; 
lean_dec(x_95);
lean_inc(x_94);
x_96 = l_Lean_Syntax_isOfKind(x_94, x_69);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_93);
x_97 = lean_box(0);
x_10 = x_97;
goto block_58;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Lean_Syntax_getArgs(x_94);
x_99 = lean_array_get_size(x_98);
lean_dec(x_98);
x_100 = lean_nat_dec_eq(x_99, x_67);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_94);
lean_dec(x_93);
x_101 = lean_box(0);
x_10 = x_101;
goto block_58;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_Syntax_getArg(x_94, x_76);
lean_dec(x_94);
x_103 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_inc(x_102);
x_104 = l_Lean_Syntax_isOfKind(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_93);
x_105 = lean_box(0);
x_10 = x_105;
goto block_58;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = l_Lean_Syntax_getArgs(x_102);
x_107 = lean_array_get_size(x_106);
lean_dec(x_106);
x_108 = lean_nat_dec_eq(x_107, x_83);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_102);
lean_dec(x_93);
x_109 = lean_box(0);
x_10 = x_109;
goto block_58;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = l_Lean_Syntax_getArg(x_102, x_67);
lean_dec(x_102);
x_111 = lean_unsigned_to_nat(4u);
x_112 = l_Lean_Syntax_getArg(x_1, x_111);
x_113 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
lean_inc(x_112);
x_114 = l_Lean_Syntax_isOfKind(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_93);
x_115 = lean_box(0);
x_10 = x_115;
goto block_58;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = l_Lean_Syntax_getArgs(x_112);
x_117 = lean_array_get_size(x_116);
lean_dec(x_116);
x_118 = lean_nat_dec_eq(x_117, x_83);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_93);
x_119 = lean_box(0);
x_10 = x_119;
goto block_58;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_Syntax_getArg(x_112, x_76);
lean_inc(x_120);
x_121 = l_Lean_Syntax_isOfKind(x_120, x_69);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_120);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_93);
x_122 = lean_box(0);
x_10 = x_122;
goto block_58;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = l_Lean_Syntax_getArgs(x_120);
lean_dec(x_120);
x_124 = lean_array_get_size(x_123);
lean_dec(x_123);
x_125 = lean_nat_dec_eq(x_124, x_76);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = lean_nat_dec_eq(x_124, x_67);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_93);
x_127 = lean_box(0);
x_10 = x_127;
goto block_58;
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l_Lean_Syntax_getArg(x_112, x_67);
lean_dec(x_112);
lean_inc(x_128);
x_129 = l_Lean_Syntax_isOfKind(x_128, x_69);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_128);
lean_dec(x_110);
lean_dec(x_93);
x_130 = lean_box(0);
x_10 = x_130;
goto block_58;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = l_Lean_Syntax_getArgs(x_128);
x_132 = lean_array_get_size(x_131);
lean_dec(x_131);
x_133 = lean_nat_dec_eq(x_132, x_67);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_128);
lean_dec(x_110);
lean_dec(x_93);
x_134 = lean_box(0);
x_10 = x_134;
goto block_58;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = l_Lean_Syntax_getArg(x_128, x_76);
lean_dec(x_128);
x_136 = l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
lean_inc(x_135);
x_137 = l_Lean_Syntax_isOfKind(x_135, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_93);
x_138 = lean_box(0);
x_10 = x_138;
goto block_58;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = l_Lean_Syntax_getArgs(x_135);
x_140 = lean_array_get_size(x_139);
lean_dec(x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_dec_eq(x_140, x_141);
lean_dec(x_140);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_93);
x_143 = lean_box(0);
x_10 = x_143;
goto block_58;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lean_Syntax_getArg(x_135, x_76);
lean_inc(x_144);
x_145 = l_Lean_Syntax_isOfKind(x_144, x_69);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_144);
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_93);
x_146 = lean_box(0);
x_10 = x_146;
goto block_58;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l_Lean_Syntax_getArgs(x_144);
x_148 = lean_array_get_size(x_147);
lean_dec(x_147);
x_149 = lean_nat_dec_eq(x_148, x_67);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_144);
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_93);
x_150 = lean_box(0);
x_10 = x_150;
goto block_58;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = l_Lean_Syntax_getArg(x_144, x_76);
lean_dec(x_144);
x_152 = l_Lean_identKind___closed__2;
lean_inc(x_151);
x_153 = l_Lean_Syntax_isOfKind(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_135);
lean_dec(x_110);
lean_dec(x_93);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_154 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_168; 
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_158 = l_Lean_Syntax_getArg(x_1, x_83);
x_168 = l_Lean_Syntax_isNone(x_158);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_array_get_size(x_157);
x_170 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__2(x_1, x_157, x_169, x_76);
lean_dec(x_169);
lean_dec(x_157);
x_159 = x_170;
goto block_167;
}
else
{
uint8_t x_171; 
lean_dec(x_157);
x_171 = 0;
x_159 = x_171;
goto block_167;
}
block_167:
{
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_158);
x_160 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
lean_dec(x_1);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_2);
lean_dec(x_1);
x_161 = l_Lean_Elab_Term_elabMatch___closed__3;
x_162 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_158, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_158);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
return x_162;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_162);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_154, 1);
lean_inc(x_172);
lean_dec(x_154);
x_173 = lean_ctor_get(x_155, 0);
lean_inc(x_173);
lean_dec(x_155);
x_174 = !lean_is_exclusive(x_3);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_3, 6);
lean_inc(x_173);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_176, 1, x_173);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_3, 6, x_177);
x_178 = 1;
x_179 = l_Lean_Elab_Term_elabTerm(x_173, x_2, x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_172);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; 
x_180 = lean_ctor_get(x_3, 0);
x_181 = lean_ctor_get(x_3, 1);
x_182 = lean_ctor_get(x_3, 2);
x_183 = lean_ctor_get(x_3, 3);
x_184 = lean_ctor_get(x_3, 4);
x_185 = lean_ctor_get(x_3, 5);
x_186 = lean_ctor_get(x_3, 6);
x_187 = lean_ctor_get(x_3, 7);
x_188 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_189 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_3);
lean_inc(x_173);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_173);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_186);
x_192 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_181);
lean_ctor_set(x_192, 2, x_182);
lean_ctor_set(x_192, 3, x_183);
lean_ctor_set(x_192, 4, x_184);
lean_ctor_set(x_192, 5, x_185);
lean_ctor_set(x_192, 6, x_191);
lean_ctor_set(x_192, 7, x_187);
lean_ctor_set_uint8(x_192, sizeof(void*)*8, x_188);
lean_ctor_set_uint8(x_192, sizeof(void*)*8 + 1, x_189);
x_193 = 1;
x_194 = l_Lean_Elab_Term_elabTerm(x_173, x_2, x_193, x_192, x_4, x_5, x_6, x_7, x_8, x_172);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_154);
if (x_195 == 0)
{
return x_154;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_154, 0);
x_197 = lean_ctor_get(x_154, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_154);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Lean_Syntax_getArg(x_135, x_83);
lean_dec(x_135);
x_200 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(x_1, x_93, x_151, x_110, x_199, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_200;
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
lean_object* x_201; uint8_t x_202; 
lean_dec(x_124);
x_201 = l_Lean_Syntax_getArg(x_112, x_67);
lean_dec(x_112);
lean_inc(x_201);
x_202 = l_Lean_Syntax_isOfKind(x_201, x_69);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_201);
lean_dec(x_110);
lean_dec(x_93);
x_203 = lean_box(0);
x_10 = x_203;
goto block_58;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_204 = l_Lean_Syntax_getArgs(x_201);
x_205 = lean_array_get_size(x_204);
lean_dec(x_204);
x_206 = lean_nat_dec_eq(x_205, x_67);
lean_dec(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
lean_dec(x_201);
lean_dec(x_110);
lean_dec(x_93);
x_207 = lean_box(0);
x_10 = x_207;
goto block_58;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = l_Lean_Syntax_getArg(x_201, x_76);
lean_dec(x_201);
x_209 = l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
lean_inc(x_208);
x_210 = l_Lean_Syntax_isOfKind(x_208, x_209);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_208);
lean_dec(x_110);
lean_dec(x_93);
x_211 = lean_box(0);
x_10 = x_211;
goto block_58;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_212 = l_Lean_Syntax_getArgs(x_208);
x_213 = lean_array_get_size(x_212);
lean_dec(x_212);
x_214 = lean_unsigned_to_nat(3u);
x_215 = lean_nat_dec_eq(x_213, x_214);
lean_dec(x_213);
if (x_215 == 0)
{
lean_object* x_216; 
lean_dec(x_208);
lean_dec(x_110);
lean_dec(x_93);
x_216 = lean_box(0);
x_10 = x_216;
goto block_58;
}
else
{
lean_object* x_217; uint8_t x_218; 
x_217 = l_Lean_Syntax_getArg(x_208, x_76);
lean_inc(x_217);
x_218 = l_Lean_Syntax_isOfKind(x_217, x_69);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_217);
lean_dec(x_208);
lean_dec(x_110);
lean_dec(x_93);
x_219 = lean_box(0);
x_10 = x_219;
goto block_58;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = l_Lean_Syntax_getArgs(x_217);
x_221 = lean_array_get_size(x_220);
lean_dec(x_220);
x_222 = lean_nat_dec_eq(x_221, x_67);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
lean_dec(x_217);
lean_dec(x_208);
lean_dec(x_110);
lean_dec(x_93);
x_223 = lean_box(0);
x_10 = x_223;
goto block_58;
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = l_Lean_Syntax_getArg(x_217, x_76);
lean_dec(x_217);
x_225 = l_Lean_identKind___closed__2;
lean_inc(x_224);
x_226 = l_Lean_Syntax_isOfKind(x_224, x_225);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_224);
lean_dec(x_208);
lean_dec(x_110);
lean_dec(x_93);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_227 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_241; 
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_231 = l_Lean_Syntax_getArg(x_1, x_83);
x_241 = l_Lean_Syntax_isNone(x_231);
if (x_241 == 0)
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_array_get_size(x_230);
x_243 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__3(x_1, x_230, x_242, x_76);
lean_dec(x_242);
lean_dec(x_230);
x_232 = x_243;
goto block_240;
}
else
{
uint8_t x_244; 
lean_dec(x_230);
x_244 = 0;
x_232 = x_244;
goto block_240;
}
block_240:
{
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_231);
x_233 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_229);
lean_dec(x_1);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
lean_dec(x_2);
lean_dec(x_1);
x_234 = l_Lean_Elab_Term_elabMatch___closed__3;
x_235 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_231, x_234, x_3, x_4, x_5, x_6, x_7, x_8, x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_231);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
return x_235;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_235);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_245 = lean_ctor_get(x_227, 1);
lean_inc(x_245);
lean_dec(x_227);
x_246 = lean_ctor_get(x_228, 0);
lean_inc(x_246);
lean_dec(x_228);
x_247 = !lean_is_exclusive(x_3);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_3, 6);
lean_inc(x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set(x_249, 1, x_246);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
lean_ctor_set(x_3, 6, x_250);
x_251 = 1;
x_252 = l_Lean_Elab_Term_elabTerm(x_246, x_2, x_251, x_3, x_4, x_5, x_6, x_7, x_8, x_245);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; 
x_253 = lean_ctor_get(x_3, 0);
x_254 = lean_ctor_get(x_3, 1);
x_255 = lean_ctor_get(x_3, 2);
x_256 = lean_ctor_get(x_3, 3);
x_257 = lean_ctor_get(x_3, 4);
x_258 = lean_ctor_get(x_3, 5);
x_259 = lean_ctor_get(x_3, 6);
x_260 = lean_ctor_get(x_3, 7);
x_261 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_262 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_3);
lean_inc(x_246);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_1);
lean_ctor_set(x_263, 1, x_246);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_259);
x_265 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_254);
lean_ctor_set(x_265, 2, x_255);
lean_ctor_set(x_265, 3, x_256);
lean_ctor_set(x_265, 4, x_257);
lean_ctor_set(x_265, 5, x_258);
lean_ctor_set(x_265, 6, x_264);
lean_ctor_set(x_265, 7, x_260);
lean_ctor_set_uint8(x_265, sizeof(void*)*8, x_261);
lean_ctor_set_uint8(x_265, sizeof(void*)*8 + 1, x_262);
x_266 = 1;
x_267 = l_Lean_Elab_Term_elabTerm(x_246, x_2, x_266, x_265, x_4, x_5, x_6, x_7, x_8, x_245);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_227);
if (x_268 == 0)
{
return x_227;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_227, 0);
x_270 = lean_ctor_get(x_227, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_227);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = l_Lean_Syntax_getArg(x_208, x_83);
lean_dec(x_208);
x_273 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(x_1, x_93, x_224, x_110, x_272, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_273;
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
block_58:
{
lean_object* x_11; 
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_26; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_26 = l_Lean_Syntax_isNone(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_14);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__1(x_1, x_14, x_27, x_28);
lean_dec(x_27);
lean_dec(x_14);
x_17 = x_29;
goto block_25;
}
else
{
uint8_t x_30; 
lean_dec(x_14);
x_30 = 0;
x_17 = x_30;
goto block_25;
}
block_25:
{
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_elabMatch___closed__3;
x_20 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_16, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_3, 6);
lean_inc(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_3, 6, x_36);
x_37 = 1;
x_38 = l_Lean_Elab_Term_elabTerm(x_32, x_2, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_3, 2);
x_42 = lean_ctor_get(x_3, 3);
x_43 = lean_ctor_get(x_3, 4);
x_44 = lean_ctor_get(x_3, 5);
x_45 = lean_ctor_get(x_3, 6);
x_46 = lean_ctor_get(x_3, 7);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
lean_inc(x_32);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_32);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
x_51 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set(x_51, 6, x_50);
lean_ctor_set(x_51, 7, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*8, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*8 + 1, x_48);
x_52 = 1;
x_53 = l_Lean_Elab_Term_elabTerm(x_32, x_2, x_52, x_51, x_4, x_5, x_6, x_7, x_8, x_31);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_11;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_elabMatch___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
static lean_object* _init_l_Lean_Elab_Term_elabNoMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nomatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNoMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_elabNoMatch___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabNoMatch___closed__2;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
lean_inc(x_5);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_24 = lean_array_push(x_23, x_19);
x_25 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Array_empty___closed__1;
x_30 = l_Lean_mkOptionalNode___closed__1;
x_31 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(x_28, x_29, x_30, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNoMatch), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabNoMatch___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
lean_object* initialize_Lean_Elab_App(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchPatternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3);
l_Lean_Elab_Term_PatternVar_hasToString___closed__1 = _init_l_Lean_Elab_Term_PatternVar_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_PatternVar_hasToString___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind___closed__2);
res = l___private_Lean_Elab_Match_0__Lean_Elab_Term_registerAuxiliaryNodeKind(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1);
l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2);
l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_CollectPatternVars_State_found___default = _init_l_Lean_Elab_Term_CollectPatternVars_State_found___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_found___default);
l_Lean_Elab_Term_CollectPatternVars_State_vars___default = _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_vars___default);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__5 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__5);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__6 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__6);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__7 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__7);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__8 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__8);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__9 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__9);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__10 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__10);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__11 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__11);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__12 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__12);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__13 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__13);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__14 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__14);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6);
l_Lean_Elab_Term_ToDepElimPattern_State_found___default = _init_l_Lean_Elab_Term_ToDepElimPattern_State_found___default();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_State_found___default);
l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default = _init_l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2);
l_Lean_Elab_Term_ToDepElimPattern_main___closed__1 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___closed__1);
l_Lean_Elab_Term_ToDepElimPattern_main___closed__2 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___closed__2);
l_Lean_Elab_Term_ToDepElimPattern_main___closed__3 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___closed__3);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2);
l_Lean_Elab_Term_elabMatchAltView___closed__1 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__1);
l_Lean_Elab_Term_elabMatchAltView___closed__2 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__2);
l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__1 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__2 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__6 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__6);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2);
l_Lean_Elab_Term_elabMatch___closed__1 = _init_l_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch___closed__1);
l_Lean_Elab_Term_elabMatch___closed__2 = _init_l_Lean_Elab_Term_elabMatch___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch___closed__2);
l_Lean_Elab_Term_elabMatch___closed__3 = _init_l_Lean_Elab_Term_elabMatch___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch___closed__3);
l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Match_0__Lean_Elab_Term_regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabNoMatch___closed__1 = _init_l_Lean_Elab_Term_elabNoMatch___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNoMatch___closed__1);
l_Lean_Elab_Term_elabNoMatch___closed__2 = _init_l_Lean_Elab_Term_elabNoMatch___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNoMatch___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
