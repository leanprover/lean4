// Lean compiler output
// Module: Lean.Elab.Match
// Imports: Init Lean.Meta.Match.MatchPatternAttr Lean.Meta.Match.Match Lean.Elab.SyntheticMVars Lean.Elab.App Lean.Parser.Term
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__8;
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault_match__1(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__2___boxed(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14424____closed__12;
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__1;
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop(lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__4;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_tryPostpone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__9;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(size_t, size_t, lean_object*);
lean_object* l_Array_forM___at_Lean_Meta_ToHide_fixpointStep___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__3;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_Elab_Term_commitIfDidNotPostpone___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3(lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1077____closed__1;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__1;
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14424____closed__6;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_5198____spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__4;
lean_object* l_Array_forM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__1;
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14424____closed__11;
uint8_t l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3;
lean_object* l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwMVarError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12336____closed__8;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed(lean_object**);
extern lean_object* l_Lean_rootNamespace___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__2;
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__4;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___lambda__2___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
lean_object* l_Lean_Elab_Term_instToStringPatternVar_match__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isAuxDiscrName___closed__2;
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13855____closed__9;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprUnit___lambda__1___closed__1;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_getPatternVars_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14424____closed__4;
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1;
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_getNextParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView___closed__1;
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_insert___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
lean_object* l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_nomatch___elambda__1___closed__2;
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isAuxDiscrName___boxed(lean_object*);
extern lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
uint8_t l_Lean_Elab_Term_isAuxDiscrName(lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
lean_object* l_Lean_Elab_Term_isAuxDiscrName___closed__1;
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_State_found___default;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType___boxed(lean_object*);
lean_object* l_Array_forM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__10;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_match__1(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed__const__1;
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__2(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_autoBoundImplicitLocal___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4;
extern lean_object* l_Lean_Syntax_getHead_x3f___closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14424____closed__1;
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHead_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1;
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___closed__1;
lean_object* l_Array_foldlMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14424____closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2191____closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__3;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_State_found___default;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__2;
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_List_elem___at_Lean_Occurrences_contains___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId___boxed(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__5___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3;
lean_object* l_Array_foldlMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1(lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__2(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_Lean_Syntax_getHead_x3f___closed__3;
lean_object* l_Lean_Elab_Term_instToStringPatternVar(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3;
lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
lean_object* l_Lean_Elab_Term_instToStringPatternVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__4;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1;
lean_object* l_Lean_Elab_Term_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2191____closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern(lean_object*);
lean_object* l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_scientificLitKind;
extern lean_object* l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_match__1___rarg(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
lean_object* l_Lean_Elab_Term_CollectPatternVars_State_vars___default;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__3;
lean_object* l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*);
uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__5;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__1;
extern lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
extern lean_object* l_Lean_Elab_Term_resolveId_x3f___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__7;
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1(lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getEvenElems___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1398____closed__8;
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__2;
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
extern lean_object* l_Lean_Elab_Term_instInhabitedNamedArg;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3;
lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2;
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_getHead_x3f___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5;
extern lean_object* l_Lean_Syntax_getHead_x3f___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3;
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3;
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__3;
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1(lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3;
extern lean_object* l_rawNatLit___closed__5;
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__2;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_match_ignoreUnusedAlts;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_substCore___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_8841_(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601_(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105_(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__6;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__4;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instToStringPatternVar___closed__1;
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5658____closed__34;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12938____closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS(lean_object*);
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__3(lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__1;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2;
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_matchPatternAttr;
lean_object* l_Lean_Elab_Term_getPatternVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_object*);
static lean_object* _init_l_Lean_Elab_Term_instInhabitedMatchAltView___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedMatchAltView() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedMatchAltView___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Term_getMainModule___rarg(x_11, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_myMacro____x40_Init_Notation___hyg_14424____closed__1;
lean_inc(x_14);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = lean_array_push(x_22, x_3);
x_25 = l_myMacro____x40_Init_Notation___hyg_1398____closed__8;
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_array_push(x_26, x_25);
x_28 = l_myMacro____x40_Init_Notation___hyg_14424____closed__11;
lean_inc(x_14);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_27, x_29);
x_31 = lean_array_push(x_30, x_2);
x_32 = l_myMacro____x40_Init_Notation___hyg_14424____closed__6;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_22, x_33);
x_35 = l_myMacro____x40_Init_Notation___hyg_14424____closed__4;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_23, x_36);
x_38 = l_myMacro____x40_Init_Notation___hyg_14424____closed__12;
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_22, x_39);
x_41 = l_Lean_nullKind___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_array_push(x_37, x_42);
x_44 = lean_array_push(x_43, x_4);
x_45 = l_myMacro____x40_Init_Notation___hyg_14424____closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_inc(x_46);
lean_inc(x_1);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_46);
lean_closure_set(x_47, 2, x_5);
x_48 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_46, x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_48;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_14 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Term_getMainModule___rarg(x_12, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_myMacro____x40_Init_Notation___hyg_14424____closed__1;
lean_inc(x_15);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Array_empty___closed__1;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_array_push(x_23, x_3);
x_26 = l_myMacro____x40_Init_Notation___hyg_1398____closed__8;
x_27 = lean_array_push(x_25, x_26);
x_28 = l_myMacro____x40_Init_Notation___hyg_13855____closed__9;
lean_inc(x_15);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_23, x_29);
x_31 = lean_array_push(x_30, x_4);
x_32 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_23, x_33);
x_35 = l_Lean_nullKind___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_27, x_36);
x_38 = l_myMacro____x40_Init_Notation___hyg_14424____closed__11;
lean_inc(x_15);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_37, x_39);
x_41 = lean_array_push(x_40, x_2);
x_42 = l_myMacro____x40_Init_Notation___hyg_14424____closed__6;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_23, x_43);
x_45 = l_myMacro____x40_Init_Notation___hyg_14424____closed__4;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_24, x_46);
x_48 = l_myMacro____x40_Init_Notation___hyg_14424____closed__12;
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_23, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_47, x_51);
x_53 = lean_array_push(x_52, x_5);
x_54 = l_myMacro____x40_Init_Notation___hyg_14424____closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_inc(x_55);
lean_inc(x_1);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_6);
x_57 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_55, x_56, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
return x_57;
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_expr_instantiate1(x_1, x_2);
x_16 = lean_array_push(x_5, x_2);
x_17 = lean_box(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid type provided to match-expression, function type with arity #");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1077____closed__1;
x_2 = l_myMacro____x40_Init_Notation___hyg_12938____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discr #");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_14, x_17);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_whnf(x_13, x_6, x_7, x_8, x_9, x_10);
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
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Elab_Term_elabTermEnsuringType(x_24, x_25, x_31, x_26, x_3, x_4, x_32, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_44; lean_object* x_45; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_64 = lean_st_ref_get(x_9, x_35);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 3);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = 0;
x_44 = x_69;
x_45 = x_68;
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_72 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_71, x_3, x_4, x_6, x_7, x_8, x_9, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_44 = x_75;
x_45 = x_74;
goto block_63;
}
block_43:
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasLooseBVars(x_23);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_box(0);
x_39 = lean_unbox(x_16);
lean_dec(x_16);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(x_23, x_34, x_18, x_20, x_15, x_39, x_38, x_3, x_4, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
lean_dec(x_23);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_16);
x_41 = lean_box(0);
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(x_23, x_34, x_18, x_20, x_15, x_31, x_41, x_3, x_4, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
lean_dec(x_23);
return x_42;
}
}
block_63:
{
if (x_44 == 0)
{
lean_dec(x_22);
x_36 = x_45;
goto block_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc(x_18);
x_46 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_18);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_substCore___lambda__1___closed__3;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_34);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_34);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_22);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_KernelException_toMessageData___closed__15;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_61 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_60, x_59, x_3, x_4, x_6, x_7, x_8, x_9, x_45);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_36 = x_62;
goto block_43;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_33);
if (x_76 == 0)
{
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_33, 0);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_33);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get_uint8(x_27, 4);
x_81 = lean_ctor_get_uint8(x_27, 5);
x_82 = lean_ctor_get_uint8(x_27, 6);
x_83 = lean_ctor_get_uint8(x_27, 7);
x_84 = lean_ctor_get_uint8(x_27, 8);
lean_dec(x_27);
x_85 = 1;
x_86 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_86, 0, x_85);
lean_ctor_set_uint8(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, 2, x_85);
lean_ctor_set_uint8(x_86, 3, x_85);
lean_ctor_set_uint8(x_86, 4, x_80);
lean_ctor_set_uint8(x_86, 5, x_81);
lean_ctor_set_uint8(x_86, 6, x_82);
lean_ctor_set_uint8(x_86, 7, x_83);
lean_ctor_set_uint8(x_86, 8, x_84);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_28);
lean_ctor_set(x_87, 2, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_88 = l_Lean_Elab_Term_elabTermEnsuringType(x_24, x_25, x_85, x_26, x_3, x_4, x_87, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_99; lean_object* x_100; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_119 = lean_st_ref_get(x_9, x_90);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 3);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_ctor_get_uint8(x_121, sizeof(void*)*1);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec(x_119);
x_124 = 0;
x_99 = x_124;
x_100 = x_123;
goto block_118;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_dec(x_119);
x_126 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_127 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_126, x_3, x_4, x_6, x_7, x_8, x_9, x_125);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_unbox(x_128);
lean_dec(x_128);
x_99 = x_130;
x_100 = x_129;
goto block_118;
}
block_98:
{
uint8_t x_92; 
x_92 = l_Lean_Expr_hasLooseBVars(x_23);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_93 = lean_box(0);
x_94 = lean_unbox(x_16);
lean_dec(x_16);
x_95 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(x_23, x_89, x_18, x_20, x_15, x_94, x_93, x_3, x_4, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
lean_dec(x_23);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_16);
x_96 = lean_box(0);
x_97 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(x_23, x_89, x_18, x_20, x_15, x_85, x_96, x_3, x_4, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
lean_dec(x_23);
return x_97;
}
}
block_118:
{
if (x_99 == 0)
{
lean_dec(x_22);
x_91 = x_100;
goto block_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_inc(x_18);
x_101 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_18);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Meta_substCore___lambda__1___closed__3;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_89);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_89);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_22);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_KernelException_toMessageData___closed__15;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_116 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_115, x_114, x_3, x_4, x_6, x_7, x_8, x_9, x_100);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_91 = x_117;
goto block_98;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_131 = lean_ctor_get(x_88, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_88, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_133 = x_88;
} else {
 lean_dec_ref(x_88);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
x_135 = lean_ctor_get(x_19, 1);
lean_inc(x_135);
lean_dec(x_19);
x_136 = lean_array_get_size(x_2);
x_137 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_136);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__2;
x_140 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__4;
x_142 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_142, x_3, x_4, x_6, x_7, x_8, x_9, x_135);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_143);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_148 = !lean_is_exclusive(x_19);
if (x_148 == 0)
{
return x_19;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_19, 0);
x_150 = lean_ctor_get(x_19, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_19);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed), 10, 5);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_7);
lean_closure_set(x_20, 3, x_8);
lean_closure_set(x_20, 4, x_18);
x_21 = lean_box_usize(x_5);
x_22 = lean_box_usize(x_4);
x_23 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__3___boxed), 13, 7);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_empty___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1;
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
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_1);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__1;
lean_inc(x_1);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(x_1, x_16, x_1, x_14, x_15, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__3(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Meta_getLocalDecl(x_9, x_4, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l_Lean_Elab_Term_isAuxDiscrName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_discr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_isAuxDiscrName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_isAuxDiscrName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Term_isAuxDiscrName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_erase_macro_scopes(x_1);
x_5 = l_Lean_Elab_Term_isAuxDiscrName___closed__2;
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_isAuxDiscrName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_isAuxDiscrName(x_1);
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
x_15 = l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Lean_Meta_getLocalDecl(x_18, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_6);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_LocalDecl_userName(x_21);
x_23 = l_Lean_Elab_Term_isAuxDiscrName(x_22);
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
x_28 = l_Lean_Elab_Term_isAuxDiscrName(x_27);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc(x_2);
x_16 = l_Array_insertAt___rarg(x_13, x_15, x_2);
lean_dec(x_15);
lean_ctor_set(x_11, 1, x_16);
x_17 = 1;
x_18 = x_4 + x_17;
x_19 = x_11;
x_20 = lean_array_uset(x_10, x_4, x_19);
x_4 = x_18;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
x_24 = lean_ctor_get(x_11, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
lean_inc(x_2);
x_27 = l_Array_insertAt___rarg(x_23, x_26, x_2);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_24);
x_29 = 1;
x_30 = x_4 + x_29;
x_31 = x_28;
x_32 = lean_array_uset(x_10, x_4, x_31);
x_4 = x_30;
x_5 = x_32;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_expr_instantiate1(x_1, x_2);
x_19 = l_Lean_Syntax_mkApp___closed__1;
x_20 = lean_array_push(x_19, x_2);
x_21 = lean_array_push(x_20, x_10);
x_22 = 0;
x_23 = 1;
lean_inc(x_13);
x_24 = l_Lean_Meta_mkForallFVars(x_21, x_18, x_22, x_23, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
x_27 = l_Lean_Meta_mkEqRefl(x_3, x_13, x_14, x_15, x_16, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_push(x_4, x_28);
x_31 = lean_array_push(x_30, x_3);
x_32 = lean_array_get_size(x_5);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = x_5;
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(x_6, x_7, x_33, x_34, x_35);
x_37 = x_36;
x_38 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(x_8, x_6, x_31, x_25, x_9, x_37, x_11, x_12, x_13, x_14, x_15, x_16, x_29);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_1);
x_17 = l_Lean_Meta_mkEq(x_1, x_9, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Syntax_getId(x_2);
x_21 = lean_box(x_8);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed), 17, 9);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_9);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_6);
lean_closure_set(x_22, 6, x_2);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_21);
x_23 = 0;
x_24 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_20, x_23, x_18, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_18 = l_Lean_instInhabitedSyntax;
x_19 = lean_array_get(x_18, x_1, x_17);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_instantiateMVars(x_21, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_24);
x_26 = l_Lean_Meta_inferType(x_24, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Meta_instantiateMVars(x_27, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_24);
x_33 = l_Lean_Meta_kabstract(x_4, x_24, x_32, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_51; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_24);
x_51 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
if (x_5 == 0)
{
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Expr_hasLooseBVars(x_34);
x_36 = x_54;
x_37 = x_52;
x_38 = x_53;
goto block_50;
}
else
{
uint8_t x_55; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
x_61 = 1;
x_36 = x_61;
x_37 = x_59;
x_38 = x_60;
goto block_50;
}
else
{
uint8_t x_62; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_51);
if (x_62 == 0)
{
return x_51;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_51, 0);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_51);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
block_50:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Syntax_getArg(x_19, x_14);
lean_dec(x_19);
x_40 = l_Lean_Syntax_isNone(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_41 = l_Lean_Syntax_getArg(x_39, x_14);
lean_dec(x_39);
x_42 = lean_box(x_36);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2___boxed), 16, 8);
lean_closure_set(x_43, 0, x_24);
lean_closure_set(x_43, 1, x_41);
lean_closure_set(x_43, 2, x_34);
lean_closure_set(x_43, 3, x_3);
lean_closure_set(x_43, 4, x_6);
lean_closure_set(x_43, 5, x_17);
lean_closure_set(x_43, 6, x_1);
lean_closure_set(x_43, 7, x_42);
x_44 = 0;
x_45 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_37, x_44, x_30, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_39);
x_46 = lean_array_push(x_3, x_24);
x_47 = 0;
x_48 = l_Lean_mkForall(x_37, x_47, x_30, x_34);
x_2 = x_17;
x_3 = x_46;
x_4 = x_48;
x_5 = x_36;
x_13 = x_38;
goto _start;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_26);
if (x_74 == 0)
{
return x_26;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_26, 0);
x_76 = lean_ctor_get(x_26, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_26);
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
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_82; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_20);
if (x_82 == 0)
{
return x_20;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_20, 0);
x_84 = lean_ctor_get(x_20, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_20);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_86 = l_Array_reverse___rarg(x_3);
x_87 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_4);
lean_ctor_set(x_87, 2, x_6);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_5);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_13);
return x_88;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_1);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_3);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_26);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_3);
x_32 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_array_get_size(x_1);
x_43 = l_Array_empty___closed__1;
x_44 = 0;
x_45 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(x_1, x_42, x_43, x_4, x_44, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_45;
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_2 < x_1;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = x_3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = x_9;
lean_inc(x_4);
x_13 = l_Lean_expandMacros(x_12, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = x_14;
x_19 = lean_array_uset(x_11, x_2, x_18);
x_2 = x_17;
x_3 = x_19;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_4);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_2 < x_1;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = x_3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = x_9;
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_array_get_size(x_15);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = x_15;
x_20 = lean_box_usize(x_18);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1;
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed), 5, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_19);
x_23 = x_22;
lean_inc(x_4);
x_24 = lean_apply_2(x_23, x_4, x_5);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_12, 1, x_25);
x_27 = 1;
x_28 = x_2 + x_27;
x_29 = x_12;
x_30 = lean_array_uset(x_11, x_2, x_29);
x_2 = x_28;
x_3 = x_30;
x_5 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
x_38 = lean_ctor_get(x_12, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_39 = lean_array_get_size(x_37);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = x_37;
x_42 = lean_box_usize(x_40);
x_43 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1;
x_44 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed), 5, 3);
lean_closure_set(x_44, 0, x_42);
lean_closure_set(x_44, 1, x_43);
lean_closure_set(x_44, 2, x_41);
x_45 = x_44;
lean_inc(x_4);
x_46 = lean_apply_2(x_45, x_4, x_5);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_38);
x_50 = 1;
x_51 = x_2 + x_50;
x_52 = x_49;
x_53 = lean_array_uset(x_11, x_2, x_52);
x_2 = x_51;
x_3 = x_53;
x_5 = x_48;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_4);
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_57 = x_46;
} else {
 lean_dec_ref(x_46);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = x_1;
x_7 = lean_box_usize(x_5);
x_8 = l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1;
x_9 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed), 5, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_6);
x_10 = x_9;
x_11 = lean_apply_2(x_10, x_2, x_3);
return x_11;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Match");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.Match.0.Lean.Elab.Term.getMatchAlts");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(137u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; size_t x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = l_myMacro____x40_Init_Notation___hyg_12938____closed__9;
lean_inc(x_1);
x_12 = lean_name_mk_string(x_1, x_11);
lean_inc(x_10);
x_13 = l_Lean_Syntax_isOfKind(x_10, x_12);
lean_dec(x_12);
x_14 = 1;
x_15 = x_3 + x_14;
if (x_13 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = l_Lean_Elab_Term_instInhabitedMatchAltView;
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3;
x_18 = lean_panic_fn(x_16, x_17);
x_19 = x_18;
x_20 = lean_array_uset(x_9, x_3, x_19);
x_3 = x_15;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_10, x_24);
x_26 = l_Lean_Syntax_getArgs(x_23);
lean_dec(x_23);
x_27 = l_Array_getEvenElems___rarg(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
x_29 = x_28;
x_30 = lean_array_uset(x_9, x_3, x_29);
x_3 = x_15;
x_4 = x_30;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(138u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_myMacro____x40_Init_Notation___hyg_12938____closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = l_Array_empty___closed__1;
x_5 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_29; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_29 = l_Lean_Syntax_isNone(x_8);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_31 = l_Lean_Syntax_isOfKind(x_8, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_1);
x_32 = l_Array_empty___closed__1;
x_33 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_34 = lean_panic_fn(x_32, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = l_Lean_Syntax_getArgs(x_8);
x_36 = lean_array_get_size(x_35);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_1);
x_39 = l_Array_empty___closed__1;
x_40 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_41 = lean_panic_fn(x_39, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Syntax_getArg(x_8, x_42);
lean_dec(x_8);
x_44 = l_Lean_expandExplicitBindersAux_loop___closed__4;
lean_inc(x_43);
x_45 = l_Lean_Syntax_isOfKind(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_1);
x_46 = l_Array_empty___closed__1;
x_47 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_48 = lean_panic_fn(x_46, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_Syntax_getArg(x_43, x_37);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(0);
x_9 = x_51;
x_10 = x_50;
goto block_28;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_9 = x_53;
x_10 = x_52;
goto block_28;
}
block_28:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_myMacro____x40_Init_Notation___hyg_12938____closed__8;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = l_Array_empty___closed__1;
x_16 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_17 = lean_panic_fn(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = x_20;
x_25 = l_myMacro____x40_Init_Notation___hyg_2191____closed__2;
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(x_25, x_22, x_23, x_24);
x_27 = x_26;
return x_27;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
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
lean_object* l_Lean_Elab_Term_instToStringPatternVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_instToStringPatternVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instToStringPatternVar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_instToStringPatternVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?m");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_instToStringPatternVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep(x_6, x_5);
x_8 = l_Lean_Elab_Term_instToStringPatternVar___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_instInhabitedParserDescr___closed__1;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MVarWithIdKind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2;
x_3 = l_Lean_Parser_registerBuiltinNodeKind(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(x_1, x_2);
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
x_10 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2;
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
x_18 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2;
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
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabInaccessible___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
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
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l_Lean_Meta_getLocalDecl(x_15, x_7, x_8, x_9, x_10, x_11);
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
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed), 9, 0);
return x_2;
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
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1() {
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1;
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg___boxed), 3, 0);
return x_6;
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
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = l_Array_isEmpty___rarg(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
x_15 = l_List_isEmpty___rarg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3;
x_17 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg(x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_array_push(x_28, x_27);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_array_push(x_29, x_30);
x_32 = l_myMacro____x40_Init_NotationExtra___hyg_5658____closed__34;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_ctor_get(x_1, 6);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_Syntax_mkApp(x_33, x_34);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_empty___closed__1;
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_array_push(x_40, x_41);
x_43 = l_myMacro____x40_Init_NotationExtra___hyg_5658____closed__34;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_ctor_get(x_1, 6);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Syntax_mkApp(x_44, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_36);
return x_47;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
x_5 = l_Lean_instInhabitedLocalDecl;
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
x_19 = l_Lean_instInhabitedLocalDecl;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___lambda__2___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1;
x_2 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
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
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3;
x_3 = lean_unsigned_to_nat(282u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2;
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(x_5);
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
x_11 = l_List_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = x_14;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(x_16, x_17, x_18);
x_20 = x_19;
x_21 = lean_array_to_list(lean_box(0), x_20);
x_22 = l_List_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__2(x_21);
x_23 = l_Lean_MessageData_ofList(x_22);
lean_dec(x_22);
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_KernelException_toMessageData___closed__15;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg(x_9, x_10, x_11);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_empty___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_3, 5);
lean_dec(x_45);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
lean_ctor_set(x_3, 5, x_47);
x_48 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_53 = lean_ctor_get(x_3, 2);
x_54 = lean_ctor_get(x_3, 3);
x_55 = lean_ctor_get(x_3, 4);
x_56 = lean_ctor_get(x_3, 6);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_57 = lean_ctor_get(x_12, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_dec(x_12);
x_59 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_50);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_59, 6, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*7, x_51);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 1, x_52);
x_60 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_59, x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_60;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__2___rarg(x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
lean_inc(x_15);
x_25 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_15);
x_26 = lean_array_get_size(x_22);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_22);
x_28 = l_Array_findIdx_x3f_loop___rarg(x_22, x_25, x_26, x_27, lean_box(0));
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_29 = l_Lean_LocalDecl_binderInfo(x_15);
lean_dec(x_15);
x_30 = lean_box(x_29);
switch (lean_obj_tag(x_30)) {
case 1:
{
lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_2 = x_32;
x_10 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
case 3:
{
lean_object* x_39; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_39 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_2 = x_40;
x_10 = x_41;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
default: 
{
lean_object* x_47; 
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_47 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_2 = x_48;
x_10 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_15);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_14, 6);
lean_dec(x_56);
x_57 = lean_ctor_get(x_14, 5);
lean_dec(x_57);
x_58 = lean_ctor_get(x_14, 4);
lean_dec(x_58);
x_59 = lean_ctor_get(x_14, 3);
lean_dec(x_59);
x_60 = lean_ctor_get(x_14, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_14, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_14, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_28, 0);
lean_inc(x_63);
lean_dec(x_28);
x_64 = l_Lean_Elab_Term_instInhabitedNamedArg;
x_65 = lean_array_get(x_64, x_22, x_63);
x_66 = l_Array_eraseIdx___rarg(x_22, x_63);
lean_dec(x_63);
lean_ctor_set(x_14, 4, x_66);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_68 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_12, x_14, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_2 = x_69;
x_10 = x_70;
goto _start;
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 0);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_14);
x_76 = lean_ctor_get(x_28, 0);
lean_inc(x_76);
lean_dec(x_28);
x_77 = l_Lean_Elab_Term_instInhabitedNamedArg;
x_78 = lean_array_get(x_77, x_22, x_76);
x_79 = l_Array_eraseIdx___rarg(x_22, x_76);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_80, 0, x_16);
lean_ctor_set(x_80, 1, x_17);
lean_ctor_set(x_80, 2, x_20);
lean_ctor_set(x_80, 3, x_21);
lean_ctor_set(x_80, 4, x_79);
lean_ctor_set(x_80, 5, x_23);
lean_ctor_set(x_80, 6, x_24);
lean_ctor_set_uint8(x_80, sizeof(void*)*7, x_18);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 1, x_19);
x_81 = lean_ctor_get(x_78, 2);
lean_inc(x_81);
lean_dec(x_78);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_82 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_12, x_80, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_2 = x_83;
x_10 = x_84;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
else
{
lean_object* x_90; 
lean_dec(x_1);
x_90 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_90;
}
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_mkConst(x_1, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_KernelException_toMessageData___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = lean_environment_find(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_box(0);
x_30 = l_Lean_mkConst(x_1, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_KernelException_toMessageData___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
lean_inc(x_7);
x_19 = l_Lean_Meta_getFVarLocalDecl(x_18, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_2 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_2, x_24);
x_2 = x_23;
x_3 = x_25;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_7);
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
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__3___rarg___lambda__1), 11, 4);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_array_get_size(x_9);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = x_9;
x_22 = lean_box_usize(x_20);
x_23 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1;
x_24 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed), 11, 3);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_21);
x_25 = x_24;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = lean_apply_8(x_25, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_empty___closed__1;
x_33 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_6);
lean_ctor_set(x_33, 5, x_7);
lean_ctor_set(x_33, 6, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 1, x_5);
x_34 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(x_8, x_33, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_28);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_st_ref_get(x_17, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_matchPatternAttr;
x_42 = l_Lean_TagAttribute_hasTag(x_41, x_40, x_2);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_43 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_39);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_empty___closed__1;
x_47 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_35);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_6);
lean_ctor_set(x_47, 5, x_7);
lean_ctor_set(x_47, 6, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 1, x_5);
x_48 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(x_8, x_47, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_39);
return x_48;
}
}
}
else
{
uint8_t x_49; 
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
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_26);
if (x_49 == 0)
{
return x_26;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_26, 0);
x_51 = lean_ctor_get(x_26, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_26);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_14);
x_17 = l_Lean_Elab_Term_resolveId_x3f(x_14, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_23);
x_24 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_ConstantInfo_type(x_25);
x_28 = lean_box(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed), 18, 8);
lean_closure_set(x_29, 0, x_25);
lean_closure_set(x_29, 1, x_23);
lean_closure_set(x_29, 2, x_14);
lean_closure_set(x_29, 3, x_15);
lean_closure_set(x_29, 4, x_28);
lean_closure_set(x_29, 5, x_2);
lean_closure_set(x_29, 6, x_3);
lean_closure_set(x_29, 7, x_4);
x_30 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(x_27, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_to_list(lean_box(0), x_4);
x_15 = l_Lean_identKind___closed__2;
lean_inc(x_2);
x_16 = l_Lean_Syntax_isOfKind(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_myMacro____x40_Init_NotationExtra___hyg_5658____closed__34;
lean_inc(x_2);
x_18 = l_Lean_Syntax_isOfKind(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_resolveId_x3f___closed__2;
x_20 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_Syntax_getArg(x_2, x_25);
lean_dec(x_2);
lean_inc(x_26);
x_27 = l_Lean_Syntax_isOfKind(x_26, x_15);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_28 = l_Lean_Elab_Term_resolveId_x3f___closed__2;
x_29 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2(x_5, x_3, x_14, x_1, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_37;
}
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2(x_5, x_3, x_14, x_1, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_41;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_1);
return x_21;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_24);
return x_25;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lean_NameSet_insert___closed__1;
x_19 = lean_box(0);
lean_inc(x_1);
x_20 = l_Std_RBNode_insert___rarg(x_18, x_17, x_1, x_19);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_set(x_4, x_24, x_16);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_NameSet_contains(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
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
x_15 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_11 = l_Lean_Elab_Term_resolveId_x3f___closed__2;
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_16 = l_Lean_Elab_Term_resolveId_x3f(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_22);
lean_inc(x_14);
x_23 = lean_environment_find(x_14, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 6)
{
lean_object* x_26; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_14);
x_26 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_25);
x_27 = l_Lean_matchPatternAttr;
x_28 = l_Lean_TagAttribute_hasTag(x_27, x_14, x_22);
lean_dec(x_14);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_1);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
}
}
else
{
uint8_t x_33; 
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
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__4;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_2 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_938____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_2 = l_rawNatLit___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l_rawNatLit___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__6___rarg(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_19 = l_Lean_addMacroScope(x_17, x_18, x_13);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_26 = l_Lean_addMacroScope(x_23, x_25, x_13);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_28 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__6___rarg(x_6, x_7, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_46 = l_Lean_addMacroScope(x_44, x_45, x_40);
x_47 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_48 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
lean_inc(x_37);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Array_empty___closed__1;
x_51 = lean_array_push(x_50, x_49);
x_52 = lean_array_push(x_50, x_34);
x_53 = lean_box(2);
x_54 = l_Lean_Syntax_mkStrLit(x_32, x_53);
lean_dec(x_32);
x_55 = lean_array_push(x_52, x_54);
x_56 = l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_37);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_50, x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_55, x_60);
x_62 = l_Lean_nullKind___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_51, x_63);
x_65 = l_myMacro____x40_Init_Notation___hyg_2191____closed__4;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_42, 0, x_66);
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_69 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_70 = l_Lean_addMacroScope(x_67, x_69, x_40);
x_71 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_72 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
lean_inc(x_37);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
x_74 = l_Array_empty___closed__1;
x_75 = lean_array_push(x_74, x_73);
x_76 = lean_array_push(x_74, x_34);
x_77 = lean_box(2);
x_78 = l_Lean_Syntax_mkStrLit(x_32, x_77);
lean_dec(x_32);
x_79 = lean_array_push(x_76, x_78);
x_80 = l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_37);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_push(x_74, x_81);
x_83 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_array_push(x_79, x_84);
x_86 = l_Lean_nullKind___closed__2;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_push(x_75, x_87);
x_89 = l_myMacro____x40_Init_Notation___hyg_2191____closed__4;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_68);
return x_91;
}
}
default: 
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__6___rarg(x_6, x_7, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_102);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_107 = l_Lean_addMacroScope(x_105, x_106, x_101);
x_108 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_109 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_inc(x_98);
x_110 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_109);
x_111 = l_Array_empty___closed__1;
x_112 = lean_array_push(x_111, x_110);
x_113 = lean_array_push(x_111, x_95);
x_114 = l_Nat_repr(x_93);
x_115 = l_Lean_numLitKind;
x_116 = lean_box(2);
x_117 = l_Lean_Syntax_mkLit(x_115, x_114, x_116);
x_118 = lean_array_push(x_113, x_117);
x_119 = l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_98);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_111, x_120);
x_122 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_array_push(x_118, x_123);
x_125 = l_Lean_nullKind___closed__2;
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_array_push(x_112, x_126);
x_128 = l_myMacro____x40_Init_Notation___hyg_2191____closed__4;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_103, 0, x_129);
return x_103;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_130 = lean_ctor_get(x_103, 0);
x_131 = lean_ctor_get(x_103, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_103);
x_132 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_133 = l_Lean_addMacroScope(x_130, x_132, x_101);
x_134 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_135 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_inc(x_98);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_98);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_135);
x_137 = l_Array_empty___closed__1;
x_138 = lean_array_push(x_137, x_136);
x_139 = lean_array_push(x_137, x_95);
x_140 = l_Nat_repr(x_93);
x_141 = l_Lean_numLitKind;
x_142 = lean_box(2);
x_143 = l_Lean_Syntax_mkLit(x_141, x_140, x_142);
x_144 = lean_array_push(x_139, x_143);
x_145 = l_myMacro____x40_Init_Notation___hyg_12938____closed__14;
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_98);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_array_push(x_137, x_146);
x_148 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_array_push(x_144, x_149);
x_151 = l_Lean_nullKind___closed__2;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_138, x_152);
x_154 = l_myMacro____x40_Init_Notation___hyg_2191____closed__4;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_131);
return x_156;
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
x_9 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
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
lean_dec(x_1);
x_12 = lean_apply_4(x_3, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg___boxed), 3, 0);
return x_6;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
x_19 = l_Lean_Syntax_getArg(x_18, x_16);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_19, x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Elab_Term_CollectPatternVars_collect(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Syntax_setArg(x_19, x_20, x_23);
lean_inc(x_25);
x_26 = l_Lean_Syntax_setArg(x_25, x_16, x_25);
x_27 = 1;
x_28 = x_2 + x_27;
x_29 = x_26;
x_30 = lean_array_uset(x_17, x_2, x_29);
x_2 = x_28;
x_3 = x_30;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = l_Lean_instInhabitedSyntax;
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_12, x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = x_15;
x_19 = lean_box_usize(x_17);
x_20 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1;
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4___boxed), 11, 3);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_18);
x_22 = x_21;
x_23 = lean_apply_8(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_nullKind;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_set(x_1, x_13, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = l_Lean_nullKind;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_array_set(x_1, x_13, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, notation is ambiguous");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_root_.namedPattern");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_rootNamespace___closed__2;
x_2 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
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
x_12 = l_myMacro____x40_Init_Notation___hyg_2191____closed__4;
x_13 = lean_name_eq(x_10, x_12);
if (x_13 == 0)
{
uint8_t x_1224; 
x_1224 = 0;
x_14 = x_1224;
goto block_1223;
}
else
{
uint8_t x_1225; 
x_1225 = 1;
x_14 = x_1225;
goto block_1223;
}
block_1223:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_7, 3);
x_17 = l_Lean_replaceRef(x_1, x_16);
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
x_30 = lean_ctor_get(x_3, 4);
lean_dec(x_30);
lean_ctor_set(x_3, 4, x_22);
if (x_14 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_32 = lean_name_eq(x_10, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__2;
x_34 = lean_name_eq(x_10, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_36 = lean_name_eq(x_10, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_myMacro____x40_Init_Notation___hyg_12336____closed__8;
x_38 = lean_name_eq(x_10, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_11);
x_39 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_40 = lean_name_eq(x_10, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_42 = lean_name_eq(x_10, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
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
x_49 = l_Lean_scientificLitKind;
x_50 = lean_name_eq(x_10, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_charLitKind;
x_52 = lean_name_eq(x_10, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_free_object(x_25);
x_53 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_54 = lean_name_eq(x_10, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_1);
x_55 = l_Lean_choiceKind;
x_56 = lean_name_eq(x_10, x_55);
lean_dec(x_10);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_59 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_2);
x_60 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_60;
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_25);
lean_dec(x_10);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Syntax_getArg(x_1, x_61);
lean_inc(x_7);
lean_inc(x_62);
x_63 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_unsigned_to_nat(2u);
x_66 = l_Lean_Syntax_getArg(x_1, x_65);
x_67 = !lean_is_exclusive(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_1, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_1, 0);
lean_dec(x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_70 = l_Lean_Elab_Term_CollectPatternVars_collect(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_7, x_8, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_75);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_78);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_83 = l_Lean_addMacroScope(x_81, x_82, x_77);
x_84 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_85 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_85);
x_87 = l_Array_empty___closed__1;
x_88 = lean_array_push(x_87, x_86);
x_89 = lean_array_push(x_87, x_62);
x_90 = lean_array_push(x_89, x_71);
x_91 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_91);
x_92 = lean_array_push(x_88, x_1);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_12);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_79, 0, x_93);
return x_79;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_94 = lean_ctor_get(x_79, 0);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_79);
x_96 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_97 = l_Lean_addMacroScope(x_94, x_96, x_77);
x_98 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_99 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_74);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_99);
x_101 = l_Array_empty___closed__1;
x_102 = lean_array_push(x_101, x_100);
x_103 = lean_array_push(x_101, x_62);
x_104 = lean_array_push(x_103, x_71);
x_105 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_105);
x_106 = lean_array_push(x_102, x_1);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_95);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_free_object(x_1);
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_70);
if (x_109 == 0)
{
return x_70;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_70, 0);
x_111 = lean_ctor_get(x_70, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_70);
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
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l_Lean_Elab_Term_CollectPatternVars_collect(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_7, x_8, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_121);
lean_dec(x_8);
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
x_126 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_127 = l_Lean_addMacroScope(x_123, x_126, x_120);
x_128 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_129 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_130 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_129);
x_131 = l_Array_empty___closed__1;
x_132 = lean_array_push(x_131, x_130);
x_133 = lean_array_push(x_131, x_62);
x_134 = lean_array_push(x_133, x_114);
x_135 = l_Lean_nullKind___closed__2;
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = lean_array_push(x_132, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_12);
lean_ctor_set(x_138, 1, x_137);
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_124);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = lean_ctor_get(x_113, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_113, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_142 = x_113;
} else {
 lean_dec_ref(x_113);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_63);
if (x_144 == 0)
{
return x_63;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_63, 0);
x_146 = lean_ctor_get(x_63, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_63);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_free_object(x_25);
lean_dec(x_10);
x_148 = lean_unsigned_to_nat(0u);
x_149 = l_Lean_Syntax_getArg(x_1, x_148);
lean_dec(x_1);
x_150 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_151 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_150, x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = l_Lean_instInhabitedSyntax;
x_153 = lean_array_get(x_152, x_11, x_23);
x_154 = l_Lean_Syntax_isNone(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
lean_free_object(x_25);
x_155 = !lean_is_exclusive(x_1);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_1, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_1, 0);
lean_dec(x_157);
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Lean_Syntax_getArg(x_153, x_158);
x_160 = l_Lean_Syntax_getArg(x_153, x_23);
x_161 = l_Lean_Syntax_isNone(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = l_Lean_Syntax_getArg(x_160, x_158);
lean_inc(x_162);
x_163 = l_Lean_Syntax_getKind(x_162);
x_164 = l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
x_165 = lean_name_eq(x_163, x_164);
lean_dec(x_163);
if (x_165 == 0)
{
lean_object* x_166; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_166 = l_Lean_Elab_Term_CollectPatternVars_collect(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Syntax_setArg(x_153, x_158, x_167);
x_170 = l_Lean_Syntax_getArg(x_162, x_23);
x_171 = l_Lean_Syntax_getArgs(x_170);
lean_dec(x_170);
x_172 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_173 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_171, x_172, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
lean_dec(x_171);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_175);
lean_ctor_set(x_1, 0, x_176);
x_177 = l_Lean_Syntax_setArg(x_162, x_23, x_1);
x_178 = l_Lean_Syntax_setArg(x_160, x_158, x_177);
x_179 = l_Lean_Syntax_setArg(x_169, x_23, x_178);
x_180 = lean_array_set(x_11, x_23, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_10);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_173, 0, x_181);
return x_173;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_182 = lean_ctor_get(x_173, 0);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_173);
x_184 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_182);
lean_ctor_set(x_1, 0, x_184);
x_185 = l_Lean_Syntax_setArg(x_162, x_23, x_1);
x_186 = l_Lean_Syntax_setArg(x_160, x_158, x_185);
x_187 = l_Lean_Syntax_setArg(x_169, x_23, x_186);
x_188 = lean_array_set(x_11, x_23, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_10);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_183);
return x_190;
}
}
else
{
uint8_t x_191; 
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_160);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_191 = !lean_is_exclusive(x_173);
if (x_191 == 0)
{
return x_173;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_173, 0);
x_193 = lean_ctor_get(x_173, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_173);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_162);
lean_dec(x_160);
lean_free_object(x_1);
lean_dec(x_153);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_166);
if (x_195 == 0)
{
return x_166;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_166, 0);
x_197 = lean_ctor_get(x_166, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_166);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_162);
lean_dec(x_160);
x_199 = l_Lean_Elab_Term_CollectPatternVars_collect(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = l_Lean_Syntax_setArg(x_153, x_158, x_201);
x_203 = lean_array_set(x_11, x_23, x_202);
lean_ctor_set(x_1, 1, x_203);
lean_ctor_set(x_199, 0, x_1);
return x_199;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_199, 0);
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_199);
x_206 = l_Lean_Syntax_setArg(x_153, x_158, x_204);
x_207 = lean_array_set(x_11, x_23, x_206);
lean_ctor_set(x_1, 1, x_207);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_1);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
}
else
{
uint8_t x_209; 
lean_free_object(x_1);
lean_dec(x_153);
lean_dec(x_11);
lean_dec(x_10);
x_209 = !lean_is_exclusive(x_199);
if (x_209 == 0)
{
return x_199;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_199, 0);
x_211 = lean_ctor_get(x_199, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_199);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
else
{
lean_object* x_213; 
lean_dec(x_160);
x_213 = l_Lean_Elab_Term_CollectPatternVars_collect(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = l_Lean_Syntax_setArg(x_153, x_158, x_215);
x_217 = lean_array_set(x_11, x_23, x_216);
lean_ctor_set(x_1, 1, x_217);
lean_ctor_set(x_213, 0, x_1);
return x_213;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_213, 0);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_213);
x_220 = l_Lean_Syntax_setArg(x_153, x_158, x_218);
x_221 = lean_array_set(x_11, x_23, x_220);
lean_ctor_set(x_1, 1, x_221);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_1);
lean_ctor_set(x_222, 1, x_219);
return x_222;
}
}
else
{
uint8_t x_223; 
lean_free_object(x_1);
lean_dec(x_153);
lean_dec(x_11);
lean_dec(x_10);
x_223 = !lean_is_exclusive(x_213);
if (x_223 == 0)
{
return x_213;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_213, 0);
x_225 = lean_ctor_get(x_213, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_213);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_1);
x_227 = lean_unsigned_to_nat(0u);
x_228 = l_Lean_Syntax_getArg(x_153, x_227);
x_229 = l_Lean_Syntax_getArg(x_153, x_23);
x_230 = l_Lean_Syntax_isNone(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_231 = l_Lean_Syntax_getArg(x_229, x_227);
lean_inc(x_231);
x_232 = l_Lean_Syntax_getKind(x_231);
x_233 = l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
x_234 = lean_name_eq(x_232, x_233);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_235 = l_Lean_Elab_Term_CollectPatternVars_collect(x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = l_Lean_Syntax_setArg(x_153, x_227, x_236);
x_239 = l_Lean_Syntax_getArg(x_231, x_23);
x_240 = l_Lean_Syntax_getArgs(x_239);
lean_dec(x_239);
x_241 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_242 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_240, x_241, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_237);
lean_dec(x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = l_Lean_nullKind;
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_243);
x_248 = l_Lean_Syntax_setArg(x_231, x_23, x_247);
x_249 = l_Lean_Syntax_setArg(x_229, x_227, x_248);
x_250 = l_Lean_Syntax_setArg(x_238, x_23, x_249);
x_251 = lean_array_set(x_11, x_23, x_250);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_10);
lean_ctor_set(x_252, 1, x_251);
if (lean_is_scalar(x_245)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_245;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_244);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_11);
lean_dec(x_10);
x_254 = lean_ctor_get(x_242, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_242, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_256 = x_242;
} else {
 lean_dec_ref(x_242);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_153);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_258 = lean_ctor_get(x_235, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_235, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_260 = x_235;
} else {
 lean_dec_ref(x_235);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; 
lean_dec(x_231);
lean_dec(x_229);
x_262 = l_Lean_Elab_Term_CollectPatternVars_collect(x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = l_Lean_Syntax_setArg(x_153, x_227, x_263);
x_267 = lean_array_set(x_11, x_23, x_266);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_10);
lean_ctor_set(x_268, 1, x_267);
if (lean_is_scalar(x_265)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_265;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_264);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_153);
lean_dec(x_11);
lean_dec(x_10);
x_270 = lean_ctor_get(x_262, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_262, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_272 = x_262;
} else {
 lean_dec_ref(x_262);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
else
{
lean_object* x_274; 
lean_dec(x_229);
x_274 = l_Lean_Elab_Term_CollectPatternVars_collect(x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
x_278 = l_Lean_Syntax_setArg(x_153, x_227, x_275);
x_279 = lean_array_set(x_11, x_23, x_278);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_10);
lean_ctor_set(x_280, 1, x_279);
if (lean_is_scalar(x_277)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_277;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_276);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_153);
lean_dec(x_11);
lean_dec(x_10);
x_282 = lean_ctor_get(x_274, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_274, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_284 = x_274;
} else {
 lean_dec_ref(x_274);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
}
}
else
{
lean_dec(x_153);
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
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
lean_dec(x_3);
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_286 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_27);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_st_ref_get(x_8, x_288);
lean_dec(x_8);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_st_ref_take(x_2, x_290);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = !lean_is_exclusive(x_292);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_295 = lean_ctor_get(x_292, 1);
x_296 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_287);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_298 = lean_array_push(x_295, x_297);
lean_ctor_set(x_292, 1, x_298);
x_299 = lean_st_ref_set(x_2, x_292, x_293);
lean_dec(x_2);
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_299, 0);
lean_dec(x_301);
lean_ctor_set(x_299, 0, x_287);
return x_299;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_287);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_304 = lean_ctor_get(x_292, 0);
x_305 = lean_ctor_get(x_292, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_292);
x_306 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_287);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = lean_array_push(x_305, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_304);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_st_ref_set(x_2, x_309, x_293);
lean_dec(x_2);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_287);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
lean_free_object(x_25);
lean_dec(x_1);
x_314 = l_Lean_instInhabitedSyntax;
x_315 = lean_array_get(x_314, x_11, x_23);
x_316 = l_Lean_Syntax_isNone(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
lean_dec(x_11);
lean_dec(x_10);
x_317 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_318 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_315, x_317, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_315);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
return x_318;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_318, 0);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_318);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_315);
x_323 = lean_box(0);
x_324 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_323, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_324;
}
}
}
else
{
uint8_t x_325; 
lean_free_object(x_25);
x_325 = !lean_is_exclusive(x_1);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_326 = lean_ctor_get(x_1, 1);
lean_dec(x_326);
x_327 = lean_ctor_get(x_1, 0);
lean_dec(x_327);
x_328 = l_Lean_instInhabitedSyntax;
x_329 = lean_array_get(x_328, x_11, x_23);
x_330 = l_Lean_Syntax_getArgs(x_329);
lean_dec(x_329);
x_331 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_332 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_330, x_331, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_330);
if (lean_obj_tag(x_332) == 0)
{
uint8_t x_333; 
x_333 = !lean_is_exclusive(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_334);
lean_ctor_set(x_1, 0, x_335);
x_336 = lean_array_set(x_11, x_23, x_1);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_10);
lean_ctor_set(x_337, 1, x_336);
lean_ctor_set(x_332, 0, x_337);
return x_332;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_338 = lean_ctor_get(x_332, 0);
x_339 = lean_ctor_get(x_332, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_332);
x_340 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_338);
lean_ctor_set(x_1, 0, x_340);
x_341 = lean_array_set(x_11, x_23, x_1);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_10);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_339);
return x_343;
}
}
else
{
uint8_t x_344; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
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
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_1);
x_348 = l_Lean_instInhabitedSyntax;
x_349 = lean_array_get(x_348, x_11, x_23);
x_350 = l_Lean_Syntax_getArgs(x_349);
lean_dec(x_349);
x_351 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_352 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_350, x_351, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_350);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_355 = x_352;
} else {
 lean_dec_ref(x_352);
 x_355 = lean_box(0);
}
x_356 = l_Lean_nullKind;
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_353);
x_358 = lean_array_set(x_11, x_23, x_357);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_10);
lean_ctor_set(x_359, 1, x_358);
if (lean_is_scalar(x_355)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_355;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_354);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_11);
lean_dec(x_10);
x_361 = lean_ctor_get(x_352, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_352, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_363 = x_352;
} else {
 lean_dec_ref(x_352);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_365 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_366 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_365, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_1);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_367 = lean_ctor_get(x_3, 0);
x_368 = lean_ctor_get(x_3, 1);
x_369 = lean_ctor_get(x_3, 2);
x_370 = lean_ctor_get(x_3, 3);
x_371 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_372 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_373 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
x_374 = lean_ctor_get(x_3, 5);
x_375 = lean_ctor_get(x_3, 6);
x_376 = lean_ctor_get(x_3, 7);
lean_inc(x_376);
lean_inc(x_375);
lean_inc(x_374);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_3);
x_377 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_377, 0, x_367);
lean_ctor_set(x_377, 1, x_368);
lean_ctor_set(x_377, 2, x_369);
lean_ctor_set(x_377, 3, x_370);
lean_ctor_set(x_377, 4, x_22);
lean_ctor_set(x_377, 5, x_374);
lean_ctor_set(x_377, 6, x_375);
lean_ctor_set(x_377, 7, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*8, x_371);
lean_ctor_set_uint8(x_377, sizeof(void*)*8 + 1, x_372);
lean_ctor_set_uint8(x_377, sizeof(void*)*8 + 2, x_373);
if (x_14 == 0)
{
lean_object* x_378; uint8_t x_379; 
x_378 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_379 = lean_name_eq(x_10, x_378);
if (x_379 == 0)
{
lean_object* x_380; uint8_t x_381; 
x_380 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__2;
x_381 = lean_name_eq(x_10, x_380);
if (x_381 == 0)
{
lean_object* x_382; uint8_t x_383; 
x_382 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_383 = lean_name_eq(x_10, x_382);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = l_myMacro____x40_Init_Notation___hyg_12336____closed__8;
x_385 = lean_name_eq(x_10, x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
lean_dec(x_11);
x_386 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_387 = lean_name_eq(x_10, x_386);
if (x_387 == 0)
{
lean_object* x_388; uint8_t x_389; 
x_388 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_389 = lean_name_eq(x_10, x_388);
if (x_389 == 0)
{
lean_object* x_390; uint8_t x_391; 
x_390 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_391 = lean_name_eq(x_10, x_390);
if (x_391 == 0)
{
lean_object* x_392; uint8_t x_393; 
x_392 = l_Lean_strLitKind;
x_393 = lean_name_eq(x_10, x_392);
if (x_393 == 0)
{
lean_object* x_394; uint8_t x_395; 
x_394 = l_Lean_numLitKind;
x_395 = lean_name_eq(x_10, x_394);
if (x_395 == 0)
{
lean_object* x_396; uint8_t x_397; 
x_396 = l_Lean_scientificLitKind;
x_397 = lean_name_eq(x_10, x_396);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; 
x_398 = l_Lean_charLitKind;
x_399 = lean_name_eq(x_10, x_398);
if (x_399 == 0)
{
lean_object* x_400; uint8_t x_401; 
lean_free_object(x_25);
x_400 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_401 = lean_name_eq(x_10, x_400);
if (x_401 == 0)
{
lean_object* x_402; uint8_t x_403; 
lean_dec(x_1);
x_402 = l_Lean_choiceKind;
x_403 = lean_name_eq(x_10, x_402);
lean_dec(x_10);
if (x_403 == 0)
{
lean_object* x_404; 
x_404 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_377);
lean_dec(x_2);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; 
x_405 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_406 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_405, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_377);
lean_dec(x_2);
return x_406;
}
}
else
{
lean_object* x_407; 
lean_dec(x_10);
lean_dec(x_2);
x_407 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_407;
}
}
else
{
lean_dec(x_377);
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
lean_dec(x_377);
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
lean_dec(x_377);
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
lean_dec(x_377);
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
lean_dec(x_377);
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
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_free_object(x_25);
lean_dec(x_10);
x_408 = lean_unsigned_to_nat(0u);
x_409 = l_Lean_Syntax_getArg(x_1, x_408);
lean_inc(x_7);
lean_inc(x_409);
x_410 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_409, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = lean_unsigned_to_nat(2u);
x_413 = l_Lean_Syntax_getArg(x_1, x_412);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_414 = x_1;
} else {
 lean_dec_ref(x_1);
 x_414 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_377);
x_415 = l_Lean_Elab_Term_CollectPatternVars_collect(x_413, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_411);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_7, x_8, x_417);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lean_Elab_Term_getCurrMacroScope(x_377, x_4, x_5, x_6, x_7, x_8, x_420);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_377);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_423);
lean_dec(x_8);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_427 = x_424;
} else {
 lean_dec_ref(x_424);
 x_427 = lean_box(0);
}
x_428 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_429 = l_Lean_addMacroScope(x_425, x_428, x_422);
x_430 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_431 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_432 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_432, 0, x_419);
lean_ctor_set(x_432, 1, x_430);
lean_ctor_set(x_432, 2, x_429);
lean_ctor_set(x_432, 3, x_431);
x_433 = l_Array_empty___closed__1;
x_434 = lean_array_push(x_433, x_432);
x_435 = lean_array_push(x_433, x_409);
x_436 = lean_array_push(x_435, x_416);
x_437 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_414)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_414;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
x_439 = lean_array_push(x_434, x_438);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_12);
lean_ctor_set(x_440, 1, x_439);
if (lean_is_scalar(x_427)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_427;
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_426);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_414);
lean_dec(x_409);
lean_dec(x_377);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_442 = lean_ctor_get(x_415, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_415, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_444 = x_415;
} else {
 lean_dec_ref(x_415);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_409);
lean_dec(x_377);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_446 = lean_ctor_get(x_410, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_410, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_448 = x_410;
} else {
 lean_dec_ref(x_410);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_free_object(x_25);
lean_dec(x_10);
x_450 = lean_unsigned_to_nat(0u);
x_451 = l_Lean_Syntax_getArg(x_1, x_450);
lean_dec(x_1);
x_452 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_453 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_452, x_451, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
return x_453;
}
}
else
{
lean_object* x_454; lean_object* x_455; uint8_t x_456; 
x_454 = l_Lean_instInhabitedSyntax;
x_455 = lean_array_get(x_454, x_11, x_23);
x_456 = l_Lean_Syntax_isNone(x_455);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_457 = x_1;
} else {
 lean_dec_ref(x_1);
 x_457 = lean_box(0);
}
x_458 = lean_unsigned_to_nat(0u);
x_459 = l_Lean_Syntax_getArg(x_455, x_458);
x_460 = l_Lean_Syntax_getArg(x_455, x_23);
x_461 = l_Lean_Syntax_isNone(x_460);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_462 = l_Lean_Syntax_getArg(x_460, x_458);
lean_inc(x_462);
x_463 = l_Lean_Syntax_getKind(x_462);
x_464 = l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
x_465 = lean_name_eq(x_463, x_464);
lean_dec(x_463);
if (x_465 == 0)
{
lean_object* x_466; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_377);
lean_inc(x_2);
x_466 = l_Lean_Elab_Term_CollectPatternVars_collect(x_459, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = l_Lean_Syntax_setArg(x_455, x_458, x_467);
x_470 = l_Lean_Syntax_getArg(x_462, x_23);
x_471 = l_Lean_Syntax_getArgs(x_470);
lean_dec(x_470);
x_472 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_473 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_471, x_472, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_468);
lean_dec(x_471);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
x_477 = l_Lean_nullKind;
if (lean_is_scalar(x_457)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_457;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_474);
x_479 = l_Lean_Syntax_setArg(x_462, x_23, x_478);
x_480 = l_Lean_Syntax_setArg(x_460, x_458, x_479);
x_481 = l_Lean_Syntax_setArg(x_469, x_23, x_480);
x_482 = lean_array_set(x_11, x_23, x_481);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_10);
lean_ctor_set(x_483, 1, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_475);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_469);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_457);
lean_dec(x_11);
lean_dec(x_10);
x_485 = lean_ctor_get(x_473, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_473, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_487 = x_473;
} else {
 lean_dec_ref(x_473);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_457);
lean_dec(x_455);
lean_dec(x_377);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_489 = lean_ctor_get(x_466, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_466, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_491 = x_466;
} else {
 lean_dec_ref(x_466);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
else
{
lean_object* x_493; 
lean_dec(x_462);
lean_dec(x_460);
x_493 = l_Lean_Elab_Term_CollectPatternVars_collect(x_459, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_496 = x_493;
} else {
 lean_dec_ref(x_493);
 x_496 = lean_box(0);
}
x_497 = l_Lean_Syntax_setArg(x_455, x_458, x_494);
x_498 = lean_array_set(x_11, x_23, x_497);
if (lean_is_scalar(x_457)) {
 x_499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_499 = x_457;
}
lean_ctor_set(x_499, 0, x_10);
lean_ctor_set(x_499, 1, x_498);
if (lean_is_scalar(x_496)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_496;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_495);
return x_500;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_457);
lean_dec(x_455);
lean_dec(x_11);
lean_dec(x_10);
x_501 = lean_ctor_get(x_493, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_493, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_503 = x_493;
} else {
 lean_dec_ref(x_493);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_502);
return x_504;
}
}
}
else
{
lean_object* x_505; 
lean_dec(x_460);
x_505 = l_Lean_Elab_Term_CollectPatternVars_collect(x_459, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_508 = x_505;
} else {
 lean_dec_ref(x_505);
 x_508 = lean_box(0);
}
x_509 = l_Lean_Syntax_setArg(x_455, x_458, x_506);
x_510 = lean_array_set(x_11, x_23, x_509);
if (lean_is_scalar(x_457)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_457;
}
lean_ctor_set(x_511, 0, x_10);
lean_ctor_set(x_511, 1, x_510);
if (lean_is_scalar(x_508)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_508;
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_507);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_457);
lean_dec(x_455);
lean_dec(x_11);
lean_dec(x_10);
x_513 = lean_ctor_get(x_505, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_505, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_515 = x_505;
} else {
 lean_dec_ref(x_505);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
}
else
{
lean_dec(x_455);
lean_dec(x_377);
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
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_377);
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_517 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_27);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_520 = lean_st_ref_get(x_8, x_519);
lean_dec(x_8);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
x_522 = lean_st_ref_take(x_2, x_521);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_523, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_527 = x_523;
} else {
 lean_dec_ref(x_523);
 x_527 = lean_box(0);
}
x_528 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_518);
x_529 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_529, 0, x_528);
x_530 = lean_array_push(x_526, x_529);
if (lean_is_scalar(x_527)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_527;
}
lean_ctor_set(x_531, 0, x_525);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_st_ref_set(x_2, x_531, x_524);
lean_dec(x_2);
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_534 = x_532;
} else {
 lean_dec_ref(x_532);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_518);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
lean_free_object(x_25);
lean_dec(x_1);
x_536 = l_Lean_instInhabitedSyntax;
x_537 = lean_array_get(x_536, x_11, x_23);
x_538 = l_Lean_Syntax_isNone(x_537);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_11);
lean_dec(x_10);
x_539 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_540 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_537, x_539, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_377);
lean_dec(x_2);
lean_dec(x_537);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_543 = x_540;
} else {
 lean_dec_ref(x_540);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_537);
x_545 = lean_box(0);
x_546 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_545, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
return x_546;
}
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_547 = x_1;
} else {
 lean_dec_ref(x_1);
 x_547 = lean_box(0);
}
x_548 = l_Lean_instInhabitedSyntax;
x_549 = lean_array_get(x_548, x_11, x_23);
x_550 = l_Lean_Syntax_getArgs(x_549);
lean_dec(x_549);
x_551 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_552 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_550, x_551, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_550);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_555 = x_552;
} else {
 lean_dec_ref(x_552);
 x_555 = lean_box(0);
}
x_556 = l_Lean_nullKind;
if (lean_is_scalar(x_547)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_547;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_553);
x_558 = lean_array_set(x_11, x_23, x_557);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_10);
lean_ctor_set(x_559, 1, x_558);
if (lean_is_scalar(x_555)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_555;
}
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_554);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_547);
lean_dec(x_11);
lean_dec(x_10);
x_561 = lean_ctor_get(x_552, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_552, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_563 = x_552;
} else {
 lean_dec_ref(x_552);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_562);
return x_564;
}
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_565 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_566 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_565, x_1, x_2, x_377, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_1);
return x_566;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; uint8_t x_573; uint8_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_567 = lean_ctor_get(x_25, 1);
lean_inc(x_567);
lean_dec(x_25);
x_568 = lean_ctor_get(x_3, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_3, 1);
lean_inc(x_569);
x_570 = lean_ctor_get(x_3, 2);
lean_inc(x_570);
x_571 = lean_ctor_get(x_3, 3);
lean_inc(x_571);
x_572 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_573 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_574 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
x_575 = lean_ctor_get(x_3, 5);
lean_inc(x_575);
x_576 = lean_ctor_get(x_3, 6);
lean_inc(x_576);
x_577 = lean_ctor_get(x_3, 7);
lean_inc(x_577);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_578 = x_3;
} else {
 lean_dec_ref(x_3);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(0, 8, 3);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_568);
lean_ctor_set(x_579, 1, x_569);
lean_ctor_set(x_579, 2, x_570);
lean_ctor_set(x_579, 3, x_571);
lean_ctor_set(x_579, 4, x_22);
lean_ctor_set(x_579, 5, x_575);
lean_ctor_set(x_579, 6, x_576);
lean_ctor_set(x_579, 7, x_577);
lean_ctor_set_uint8(x_579, sizeof(void*)*8, x_572);
lean_ctor_set_uint8(x_579, sizeof(void*)*8 + 1, x_573);
lean_ctor_set_uint8(x_579, sizeof(void*)*8 + 2, x_574);
if (x_14 == 0)
{
lean_object* x_580; uint8_t x_581; 
x_580 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_581 = lean_name_eq(x_10, x_580);
if (x_581 == 0)
{
lean_object* x_582; uint8_t x_583; 
x_582 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__2;
x_583 = lean_name_eq(x_10, x_582);
if (x_583 == 0)
{
lean_object* x_584; uint8_t x_585; 
x_584 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_585 = lean_name_eq(x_10, x_584);
if (x_585 == 0)
{
lean_object* x_586; uint8_t x_587; 
x_586 = l_myMacro____x40_Init_Notation___hyg_12336____closed__8;
x_587 = lean_name_eq(x_10, x_586);
if (x_587 == 0)
{
lean_object* x_588; uint8_t x_589; 
lean_dec(x_11);
x_588 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_589 = lean_name_eq(x_10, x_588);
if (x_589 == 0)
{
lean_object* x_590; uint8_t x_591; 
x_590 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_591 = lean_name_eq(x_10, x_590);
if (x_591 == 0)
{
lean_object* x_592; uint8_t x_593; 
x_592 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_593 = lean_name_eq(x_10, x_592);
if (x_593 == 0)
{
lean_object* x_594; uint8_t x_595; 
x_594 = l_Lean_strLitKind;
x_595 = lean_name_eq(x_10, x_594);
if (x_595 == 0)
{
lean_object* x_596; uint8_t x_597; 
x_596 = l_Lean_numLitKind;
x_597 = lean_name_eq(x_10, x_596);
if (x_597 == 0)
{
lean_object* x_598; uint8_t x_599; 
x_598 = l_Lean_scientificLitKind;
x_599 = lean_name_eq(x_10, x_598);
if (x_599 == 0)
{
lean_object* x_600; uint8_t x_601; 
x_600 = l_Lean_charLitKind;
x_601 = lean_name_eq(x_10, x_600);
if (x_601 == 0)
{
lean_object* x_602; uint8_t x_603; 
x_602 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_603 = lean_name_eq(x_10, x_602);
if (x_603 == 0)
{
lean_object* x_604; uint8_t x_605; 
lean_dec(x_1);
x_604 = l_Lean_choiceKind;
x_605 = lean_name_eq(x_10, x_604);
lean_dec(x_10);
if (x_605 == 0)
{
lean_object* x_606; 
x_606 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_579);
lean_dec(x_2);
return x_606;
}
else
{
lean_object* x_607; lean_object* x_608; 
x_607 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_608 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_607, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_579);
lean_dec(x_2);
return x_608;
}
}
else
{
lean_object* x_609; 
lean_dec(x_10);
lean_dec(x_2);
x_609 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_609;
}
}
else
{
lean_object* x_610; 
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_1);
lean_ctor_set(x_610, 1, x_567);
return x_610;
}
}
else
{
lean_object* x_611; 
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_1);
lean_ctor_set(x_611, 1, x_567);
return x_611;
}
}
else
{
lean_object* x_612; 
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_1);
lean_ctor_set(x_612, 1, x_567);
return x_612;
}
}
else
{
lean_object* x_613; 
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_1);
lean_ctor_set(x_613, 1, x_567);
return x_613;
}
}
else
{
lean_object* x_614; 
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_1);
lean_ctor_set(x_614, 1, x_567);
return x_614;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_10);
x_615 = lean_unsigned_to_nat(0u);
x_616 = l_Lean_Syntax_getArg(x_1, x_615);
lean_inc(x_7);
lean_inc(x_616);
x_617 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_616, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_619 = lean_unsigned_to_nat(2u);
x_620 = l_Lean_Syntax_getArg(x_1, x_619);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_621 = x_1;
} else {
 lean_dec_ref(x_1);
 x_621 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_579);
x_622 = l_Lean_Elab_Term_CollectPatternVars_collect(x_620, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_618);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
x_625 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_7, x_8, x_624);
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
lean_dec(x_625);
x_628 = l_Lean_Elab_Term_getCurrMacroScope(x_579, x_4, x_5, x_6, x_7, x_8, x_627);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_579);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
lean_dec(x_628);
x_631 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_630);
lean_dec(x_8);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
x_635 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_636 = l_Lean_addMacroScope(x_632, x_635, x_629);
x_637 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_638 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_639 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_639, 0, x_626);
lean_ctor_set(x_639, 1, x_637);
lean_ctor_set(x_639, 2, x_636);
lean_ctor_set(x_639, 3, x_638);
x_640 = l_Array_empty___closed__1;
x_641 = lean_array_push(x_640, x_639);
x_642 = lean_array_push(x_640, x_616);
x_643 = lean_array_push(x_642, x_623);
x_644 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_621)) {
 x_645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_645 = x_621;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_643);
x_646 = lean_array_push(x_641, x_645);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_12);
lean_ctor_set(x_647, 1, x_646);
if (lean_is_scalar(x_634)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_634;
}
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_633);
return x_648;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_621);
lean_dec(x_616);
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_649 = lean_ctor_get(x_622, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_622, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_651 = x_622;
} else {
 lean_dec_ref(x_622);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_616);
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_653 = lean_ctor_get(x_617, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_617, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_655 = x_617;
} else {
 lean_dec_ref(x_617);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_10);
x_657 = lean_unsigned_to_nat(0u);
x_658 = l_Lean_Syntax_getArg(x_1, x_657);
lean_dec(x_1);
x_659 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_660 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_659, x_658, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_661 = l_Lean_instInhabitedSyntax;
x_662 = lean_array_get(x_661, x_11, x_23);
x_663 = l_Lean_Syntax_isNone(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_664 = x_1;
} else {
 lean_dec_ref(x_1);
 x_664 = lean_box(0);
}
x_665 = lean_unsigned_to_nat(0u);
x_666 = l_Lean_Syntax_getArg(x_662, x_665);
x_667 = l_Lean_Syntax_getArg(x_662, x_23);
x_668 = l_Lean_Syntax_isNone(x_667);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; 
x_669 = l_Lean_Syntax_getArg(x_667, x_665);
lean_inc(x_669);
x_670 = l_Lean_Syntax_getKind(x_669);
x_671 = l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
x_672 = lean_name_eq(x_670, x_671);
lean_dec(x_670);
if (x_672 == 0)
{
lean_object* x_673; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_579);
lean_inc(x_2);
x_673 = l_Lean_Elab_Term_CollectPatternVars_collect(x_666, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = l_Lean_Syntax_setArg(x_662, x_665, x_674);
x_677 = l_Lean_Syntax_getArg(x_669, x_23);
x_678 = l_Lean_Syntax_getArgs(x_677);
lean_dec(x_677);
x_679 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_680 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_678, x_679, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_675);
lean_dec(x_678);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_683 = x_680;
} else {
 lean_dec_ref(x_680);
 x_683 = lean_box(0);
}
x_684 = l_Lean_nullKind;
if (lean_is_scalar(x_664)) {
 x_685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_685 = x_664;
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_681);
x_686 = l_Lean_Syntax_setArg(x_669, x_23, x_685);
x_687 = l_Lean_Syntax_setArg(x_667, x_665, x_686);
x_688 = l_Lean_Syntax_setArg(x_676, x_23, x_687);
x_689 = lean_array_set(x_11, x_23, x_688);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_10);
lean_ctor_set(x_690, 1, x_689);
if (lean_is_scalar(x_683)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_683;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_682);
return x_691;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_676);
lean_dec(x_669);
lean_dec(x_667);
lean_dec(x_664);
lean_dec(x_11);
lean_dec(x_10);
x_692 = lean_ctor_get(x_680, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_680, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_694 = x_680;
} else {
 lean_dec_ref(x_680);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_692);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_669);
lean_dec(x_667);
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_696 = lean_ctor_get(x_673, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_673, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_698 = x_673;
} else {
 lean_dec_ref(x_673);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
else
{
lean_object* x_700; 
lean_dec(x_669);
lean_dec(x_667);
x_700 = l_Lean_Elab_Term_CollectPatternVars_collect(x_666, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_703 = x_700;
} else {
 lean_dec_ref(x_700);
 x_703 = lean_box(0);
}
x_704 = l_Lean_Syntax_setArg(x_662, x_665, x_701);
x_705 = lean_array_set(x_11, x_23, x_704);
if (lean_is_scalar(x_664)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_664;
}
lean_ctor_set(x_706, 0, x_10);
lean_ctor_set(x_706, 1, x_705);
if (lean_is_scalar(x_703)) {
 x_707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_707 = x_703;
}
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_702);
return x_707;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_11);
lean_dec(x_10);
x_708 = lean_ctor_get(x_700, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_700, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_710 = x_700;
} else {
 lean_dec_ref(x_700);
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
lean_object* x_712; 
lean_dec(x_667);
x_712 = l_Lean_Elab_Term_CollectPatternVars_collect(x_666, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_715 = x_712;
} else {
 lean_dec_ref(x_712);
 x_715 = lean_box(0);
}
x_716 = l_Lean_Syntax_setArg(x_662, x_665, x_713);
x_717 = lean_array_set(x_11, x_23, x_716);
if (lean_is_scalar(x_664)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_664;
}
lean_ctor_set(x_718, 0, x_10);
lean_ctor_set(x_718, 1, x_717);
if (lean_is_scalar(x_715)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_715;
}
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_714);
return x_719;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_dec(x_664);
lean_dec(x_662);
lean_dec(x_11);
lean_dec(x_10);
x_720 = lean_ctor_get(x_712, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_712, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_722 = x_712;
} else {
 lean_dec_ref(x_712);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_723 = x_722;
}
lean_ctor_set(x_723, 0, x_720);
lean_ctor_set(x_723, 1, x_721);
return x_723;
}
}
}
else
{
lean_object* x_724; 
lean_dec(x_662);
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_1);
lean_ctor_set(x_724, 1, x_567);
return x_724;
}
}
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_579);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_725 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_567);
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
lean_dec(x_725);
x_728 = lean_st_ref_get(x_8, x_727);
lean_dec(x_8);
x_729 = lean_ctor_get(x_728, 1);
lean_inc(x_729);
lean_dec(x_728);
x_730 = lean_st_ref_take(x_2, x_729);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_733 = lean_ctor_get(x_731, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_731, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_735 = x_731;
} else {
 lean_dec_ref(x_731);
 x_735 = lean_box(0);
}
x_736 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_726);
x_737 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_737, 0, x_736);
x_738 = lean_array_push(x_734, x_737);
if (lean_is_scalar(x_735)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_735;
}
lean_ctor_set(x_739, 0, x_733);
lean_ctor_set(x_739, 1, x_738);
x_740 = lean_st_ref_set(x_2, x_739, x_732);
lean_dec(x_2);
x_741 = lean_ctor_get(x_740, 1);
lean_inc(x_741);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_742 = x_740;
} else {
 lean_dec_ref(x_740);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_726);
lean_ctor_set(x_743, 1, x_741);
return x_743;
}
}
else
{
lean_object* x_744; lean_object* x_745; uint8_t x_746; 
lean_dec(x_1);
x_744 = l_Lean_instInhabitedSyntax;
x_745 = lean_array_get(x_744, x_11, x_23);
x_746 = l_Lean_Syntax_isNone(x_745);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_11);
lean_dec(x_10);
x_747 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_748 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_745, x_747, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_579);
lean_dec(x_2);
lean_dec(x_745);
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_751 = x_748;
} else {
 lean_dec_ref(x_748);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(1, 2, 0);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_749);
lean_ctor_set(x_752, 1, x_750);
return x_752;
}
else
{
lean_object* x_753; lean_object* x_754; 
lean_dec(x_745);
x_753 = lean_box(0);
x_754 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_753, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
return x_754;
}
}
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_755 = x_1;
} else {
 lean_dec_ref(x_1);
 x_755 = lean_box(0);
}
x_756 = l_Lean_instInhabitedSyntax;
x_757 = lean_array_get(x_756, x_11, x_23);
x_758 = l_Lean_Syntax_getArgs(x_757);
lean_dec(x_757);
x_759 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_760 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_758, x_759, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
lean_dec(x_758);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_760, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 lean_ctor_release(x_760, 1);
 x_763 = x_760;
} else {
 lean_dec_ref(x_760);
 x_763 = lean_box(0);
}
x_764 = l_Lean_nullKind;
if (lean_is_scalar(x_755)) {
 x_765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_765 = x_755;
}
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_761);
x_766 = lean_array_set(x_11, x_23, x_765);
x_767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_767, 0, x_10);
lean_ctor_set(x_767, 1, x_766);
if (lean_is_scalar(x_763)) {
 x_768 = lean_alloc_ctor(0, 2, 0);
} else {
 x_768 = x_763;
}
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_762);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_755);
lean_dec(x_11);
lean_dec(x_10);
x_769 = lean_ctor_get(x_760, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_760, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 lean_ctor_release(x_760, 1);
 x_771 = x_760;
} else {
 lean_dec_ref(x_760);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
}
else
{
lean_object* x_773; lean_object* x_774; 
lean_dec(x_11);
lean_dec(x_10);
x_773 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_774 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_773, x_1, x_2, x_579, x_4, x_5, x_6, x_7, x_8, x_567);
lean_dec(x_1);
return x_774;
}
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; uint8_t x_789; uint8_t x_790; uint8_t x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_775 = lean_ctor_get(x_19, 0);
x_776 = lean_ctor_get(x_19, 1);
x_777 = lean_ctor_get(x_19, 2);
x_778 = lean_ctor_get(x_19, 3);
lean_inc(x_778);
lean_inc(x_777);
lean_inc(x_776);
lean_inc(x_775);
lean_dec(x_19);
x_779 = lean_unsigned_to_nat(1u);
x_780 = lean_nat_add(x_776, x_779);
x_781 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_781, 0, x_775);
lean_ctor_set(x_781, 1, x_780);
lean_ctor_set(x_781, 2, x_777);
lean_ctor_set(x_781, 3, x_778);
x_782 = lean_st_ref_set(x_8, x_781, x_20);
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_784 = x_782;
} else {
 lean_dec_ref(x_782);
 x_784 = lean_box(0);
}
x_785 = lean_ctor_get(x_3, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_3, 1);
lean_inc(x_786);
x_787 = lean_ctor_get(x_3, 2);
lean_inc(x_787);
x_788 = lean_ctor_get(x_3, 3);
lean_inc(x_788);
x_789 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_790 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_791 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
x_792 = lean_ctor_get(x_3, 5);
lean_inc(x_792);
x_793 = lean_ctor_get(x_3, 6);
lean_inc(x_793);
x_794 = lean_ctor_get(x_3, 7);
lean_inc(x_794);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_795 = x_3;
} else {
 lean_dec_ref(x_3);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(0, 8, 3);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_785);
lean_ctor_set(x_796, 1, x_786);
lean_ctor_set(x_796, 2, x_787);
lean_ctor_set(x_796, 3, x_788);
lean_ctor_set(x_796, 4, x_776);
lean_ctor_set(x_796, 5, x_792);
lean_ctor_set(x_796, 6, x_793);
lean_ctor_set(x_796, 7, x_794);
lean_ctor_set_uint8(x_796, sizeof(void*)*8, x_789);
lean_ctor_set_uint8(x_796, sizeof(void*)*8 + 1, x_790);
lean_ctor_set_uint8(x_796, sizeof(void*)*8 + 2, x_791);
if (x_14 == 0)
{
lean_object* x_797; uint8_t x_798; 
x_797 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_798 = lean_name_eq(x_10, x_797);
if (x_798 == 0)
{
lean_object* x_799; uint8_t x_800; 
x_799 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__2;
x_800 = lean_name_eq(x_10, x_799);
if (x_800 == 0)
{
lean_object* x_801; uint8_t x_802; 
x_801 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_802 = lean_name_eq(x_10, x_801);
if (x_802 == 0)
{
lean_object* x_803; uint8_t x_804; 
x_803 = l_myMacro____x40_Init_Notation___hyg_12336____closed__8;
x_804 = lean_name_eq(x_10, x_803);
if (x_804 == 0)
{
lean_object* x_805; uint8_t x_806; 
lean_dec(x_11);
x_805 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_806 = lean_name_eq(x_10, x_805);
if (x_806 == 0)
{
lean_object* x_807; uint8_t x_808; 
x_807 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_808 = lean_name_eq(x_10, x_807);
if (x_808 == 0)
{
lean_object* x_809; uint8_t x_810; 
x_809 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_810 = lean_name_eq(x_10, x_809);
if (x_810 == 0)
{
lean_object* x_811; uint8_t x_812; 
x_811 = l_Lean_strLitKind;
x_812 = lean_name_eq(x_10, x_811);
if (x_812 == 0)
{
lean_object* x_813; uint8_t x_814; 
x_813 = l_Lean_numLitKind;
x_814 = lean_name_eq(x_10, x_813);
if (x_814 == 0)
{
lean_object* x_815; uint8_t x_816; 
x_815 = l_Lean_scientificLitKind;
x_816 = lean_name_eq(x_10, x_815);
if (x_816 == 0)
{
lean_object* x_817; uint8_t x_818; 
x_817 = l_Lean_charLitKind;
x_818 = lean_name_eq(x_10, x_817);
if (x_818 == 0)
{
lean_object* x_819; uint8_t x_820; 
lean_dec(x_784);
x_819 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_820 = lean_name_eq(x_10, x_819);
if (x_820 == 0)
{
lean_object* x_821; uint8_t x_822; 
lean_dec(x_1);
x_821 = l_Lean_choiceKind;
x_822 = lean_name_eq(x_10, x_821);
lean_dec(x_10);
if (x_822 == 0)
{
lean_object* x_823; 
x_823 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_796);
lean_dec(x_2);
return x_823;
}
else
{
lean_object* x_824; lean_object* x_825; 
x_824 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_825 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_824, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_796);
lean_dec(x_2);
return x_825;
}
}
else
{
lean_object* x_826; 
lean_dec(x_10);
lean_dec(x_2);
x_826 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_826;
}
}
else
{
lean_object* x_827; 
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_784)) {
 x_827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_827 = x_784;
}
lean_ctor_set(x_827, 0, x_1);
lean_ctor_set(x_827, 1, x_783);
return x_827;
}
}
else
{
lean_object* x_828; 
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_784)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_784;
}
lean_ctor_set(x_828, 0, x_1);
lean_ctor_set(x_828, 1, x_783);
return x_828;
}
}
else
{
lean_object* x_829; 
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_784)) {
 x_829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_829 = x_784;
}
lean_ctor_set(x_829, 0, x_1);
lean_ctor_set(x_829, 1, x_783);
return x_829;
}
}
else
{
lean_object* x_830; 
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_784)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_784;
}
lean_ctor_set(x_830, 0, x_1);
lean_ctor_set(x_830, 1, x_783);
return x_830;
}
}
else
{
lean_object* x_831; 
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_784)) {
 x_831 = lean_alloc_ctor(0, 2, 0);
} else {
 x_831 = x_784;
}
lean_ctor_set(x_831, 0, x_1);
lean_ctor_set(x_831, 1, x_783);
return x_831;
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_784);
lean_dec(x_10);
x_832 = lean_unsigned_to_nat(0u);
x_833 = l_Lean_Syntax_getArg(x_1, x_832);
lean_inc(x_7);
lean_inc(x_833);
x_834 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_833, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_835 = lean_ctor_get(x_834, 1);
lean_inc(x_835);
lean_dec(x_834);
x_836 = lean_unsigned_to_nat(2u);
x_837 = l_Lean_Syntax_getArg(x_1, x_836);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_838 = x_1;
} else {
 lean_dec_ref(x_1);
 x_838 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_796);
x_839 = l_Lean_Elab_Term_CollectPatternVars_collect(x_837, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_835);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_7, x_8, x_841);
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_842, 1);
lean_inc(x_844);
lean_dec(x_842);
x_845 = l_Lean_Elab_Term_getCurrMacroScope(x_796, x_4, x_5, x_6, x_7, x_8, x_844);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_796);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_847);
lean_dec(x_8);
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 lean_ctor_release(x_848, 1);
 x_851 = x_848;
} else {
 lean_dec_ref(x_848);
 x_851 = lean_box(0);
}
x_852 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_853 = l_Lean_addMacroScope(x_849, x_852, x_846);
x_854 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_855 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_856 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_856, 0, x_843);
lean_ctor_set(x_856, 1, x_854);
lean_ctor_set(x_856, 2, x_853);
lean_ctor_set(x_856, 3, x_855);
x_857 = l_Array_empty___closed__1;
x_858 = lean_array_push(x_857, x_856);
x_859 = lean_array_push(x_857, x_833);
x_860 = lean_array_push(x_859, x_840);
x_861 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_838)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_838;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_860);
x_863 = lean_array_push(x_858, x_862);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_12);
lean_ctor_set(x_864, 1, x_863);
if (lean_is_scalar(x_851)) {
 x_865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_865 = x_851;
}
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_850);
return x_865;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_838);
lean_dec(x_833);
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_866 = lean_ctor_get(x_839, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_839, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_868 = x_839;
} else {
 lean_dec_ref(x_839);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
lean_dec(x_833);
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_870 = lean_ctor_get(x_834, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_834, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 x_872 = x_834;
} else {
 lean_dec_ref(x_834);
 x_872 = lean_box(0);
}
if (lean_is_scalar(x_872)) {
 x_873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_873 = x_872;
}
lean_ctor_set(x_873, 0, x_870);
lean_ctor_set(x_873, 1, x_871);
return x_873;
}
}
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_dec(x_784);
lean_dec(x_10);
x_874 = lean_unsigned_to_nat(0u);
x_875 = l_Lean_Syntax_getArg(x_1, x_874);
lean_dec(x_1);
x_876 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_877 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_876, x_875, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
return x_877;
}
}
else
{
lean_object* x_878; lean_object* x_879; uint8_t x_880; 
x_878 = l_Lean_instInhabitedSyntax;
x_879 = lean_array_get(x_878, x_11, x_779);
x_880 = l_Lean_Syntax_isNone(x_879);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; 
lean_dec(x_784);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_881 = x_1;
} else {
 lean_dec_ref(x_1);
 x_881 = lean_box(0);
}
x_882 = lean_unsigned_to_nat(0u);
x_883 = l_Lean_Syntax_getArg(x_879, x_882);
x_884 = l_Lean_Syntax_getArg(x_879, x_779);
x_885 = l_Lean_Syntax_isNone(x_884);
if (x_885 == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; 
x_886 = l_Lean_Syntax_getArg(x_884, x_882);
lean_inc(x_886);
x_887 = l_Lean_Syntax_getKind(x_886);
x_888 = l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
x_889 = lean_name_eq(x_887, x_888);
lean_dec(x_887);
if (x_889 == 0)
{
lean_object* x_890; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_796);
lean_inc(x_2);
x_890 = l_Lean_Elab_Term_CollectPatternVars_collect(x_883, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = l_Lean_Syntax_setArg(x_879, x_882, x_891);
x_894 = l_Lean_Syntax_getArg(x_886, x_779);
x_895 = l_Lean_Syntax_getArgs(x_894);
lean_dec(x_894);
x_896 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_897 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_895, x_896, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_892);
lean_dec(x_895);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
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
x_901 = l_Lean_nullKind;
if (lean_is_scalar(x_881)) {
 x_902 = lean_alloc_ctor(1, 2, 0);
} else {
 x_902 = x_881;
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_898);
x_903 = l_Lean_Syntax_setArg(x_886, x_779, x_902);
x_904 = l_Lean_Syntax_setArg(x_884, x_882, x_903);
x_905 = l_Lean_Syntax_setArg(x_893, x_779, x_904);
x_906 = lean_array_set(x_11, x_779, x_905);
x_907 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_907, 0, x_10);
lean_ctor_set(x_907, 1, x_906);
if (lean_is_scalar(x_900)) {
 x_908 = lean_alloc_ctor(0, 2, 0);
} else {
 x_908 = x_900;
}
lean_ctor_set(x_908, 0, x_907);
lean_ctor_set(x_908, 1, x_899);
return x_908;
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_dec(x_893);
lean_dec(x_886);
lean_dec(x_884);
lean_dec(x_881);
lean_dec(x_11);
lean_dec(x_10);
x_909 = lean_ctor_get(x_897, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_897, 1);
lean_inc(x_910);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_911 = x_897;
} else {
 lean_dec_ref(x_897);
 x_911 = lean_box(0);
}
if (lean_is_scalar(x_911)) {
 x_912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_912 = x_911;
}
lean_ctor_set(x_912, 0, x_909);
lean_ctor_set(x_912, 1, x_910);
return x_912;
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_886);
lean_dec(x_884);
lean_dec(x_881);
lean_dec(x_879);
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_913 = lean_ctor_get(x_890, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_890, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_915 = x_890;
} else {
 lean_dec_ref(x_890);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_913);
lean_ctor_set(x_916, 1, x_914);
return x_916;
}
}
else
{
lean_object* x_917; 
lean_dec(x_886);
lean_dec(x_884);
x_917 = l_Lean_Elab_Term_CollectPatternVars_collect(x_883, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_920 = x_917;
} else {
 lean_dec_ref(x_917);
 x_920 = lean_box(0);
}
x_921 = l_Lean_Syntax_setArg(x_879, x_882, x_918);
x_922 = lean_array_set(x_11, x_779, x_921);
if (lean_is_scalar(x_881)) {
 x_923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_923 = x_881;
}
lean_ctor_set(x_923, 0, x_10);
lean_ctor_set(x_923, 1, x_922);
if (lean_is_scalar(x_920)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_920;
}
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_919);
return x_924;
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_881);
lean_dec(x_879);
lean_dec(x_11);
lean_dec(x_10);
x_925 = lean_ctor_get(x_917, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_917, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_927 = x_917;
} else {
 lean_dec_ref(x_917);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
}
}
else
{
lean_object* x_929; 
lean_dec(x_884);
x_929 = l_Lean_Elab_Term_CollectPatternVars_collect(x_883, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_932 = x_929;
} else {
 lean_dec_ref(x_929);
 x_932 = lean_box(0);
}
x_933 = l_Lean_Syntax_setArg(x_879, x_882, x_930);
x_934 = lean_array_set(x_11, x_779, x_933);
if (lean_is_scalar(x_881)) {
 x_935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_935 = x_881;
}
lean_ctor_set(x_935, 0, x_10);
lean_ctor_set(x_935, 1, x_934);
if (lean_is_scalar(x_932)) {
 x_936 = lean_alloc_ctor(0, 2, 0);
} else {
 x_936 = x_932;
}
lean_ctor_set(x_936, 0, x_935);
lean_ctor_set(x_936, 1, x_931);
return x_936;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
lean_dec(x_881);
lean_dec(x_879);
lean_dec(x_11);
lean_dec(x_10);
x_937 = lean_ctor_get(x_929, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_929, 1);
lean_inc(x_938);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_939 = x_929;
} else {
 lean_dec_ref(x_929);
 x_939 = lean_box(0);
}
if (lean_is_scalar(x_939)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_939;
}
lean_ctor_set(x_940, 0, x_937);
lean_ctor_set(x_940, 1, x_938);
return x_940;
}
}
}
else
{
lean_object* x_941; 
lean_dec(x_879);
lean_dec(x_796);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_784)) {
 x_941 = lean_alloc_ctor(0, 2, 0);
} else {
 x_941 = x_784;
}
lean_ctor_set(x_941, 0, x_1);
lean_ctor_set(x_941, 1, x_783);
return x_941;
}
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
lean_dec(x_796);
lean_dec(x_784);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_942 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_783);
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
lean_dec(x_942);
x_945 = lean_st_ref_get(x_8, x_944);
lean_dec(x_8);
x_946 = lean_ctor_get(x_945, 1);
lean_inc(x_946);
lean_dec(x_945);
x_947 = lean_st_ref_take(x_2, x_946);
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
lean_dec(x_947);
x_950 = lean_ctor_get(x_948, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_948, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_952 = x_948;
} else {
 lean_dec_ref(x_948);
 x_952 = lean_box(0);
}
x_953 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_943);
x_954 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_954, 0, x_953);
x_955 = lean_array_push(x_951, x_954);
if (lean_is_scalar(x_952)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_952;
}
lean_ctor_set(x_956, 0, x_950);
lean_ctor_set(x_956, 1, x_955);
x_957 = lean_st_ref_set(x_2, x_956, x_949);
lean_dec(x_2);
x_958 = lean_ctor_get(x_957, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_959 = x_957;
} else {
 lean_dec_ref(x_957);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(0, 2, 0);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_943);
lean_ctor_set(x_960, 1, x_958);
return x_960;
}
}
else
{
lean_object* x_961; lean_object* x_962; uint8_t x_963; 
lean_dec(x_784);
lean_dec(x_1);
x_961 = l_Lean_instInhabitedSyntax;
x_962 = lean_array_get(x_961, x_11, x_779);
x_963 = l_Lean_Syntax_isNone(x_962);
if (x_963 == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
lean_dec(x_11);
lean_dec(x_10);
x_964 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_965 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_962, x_964, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_796);
lean_dec(x_2);
lean_dec(x_962);
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_968 = x_965;
} else {
 lean_dec_ref(x_965);
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
else
{
lean_object* x_970; lean_object* x_971; 
lean_dec(x_962);
x_970 = lean_box(0);
x_971 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_970, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
return x_971;
}
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_784);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_972 = x_1;
} else {
 lean_dec_ref(x_1);
 x_972 = lean_box(0);
}
x_973 = l_Lean_instInhabitedSyntax;
x_974 = lean_array_get(x_973, x_11, x_779);
x_975 = l_Lean_Syntax_getArgs(x_974);
lean_dec(x_974);
x_976 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_977 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_975, x_976, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
lean_dec(x_975);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
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
x_981 = l_Lean_nullKind;
if (lean_is_scalar(x_972)) {
 x_982 = lean_alloc_ctor(1, 2, 0);
} else {
 x_982 = x_972;
}
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_978);
x_983 = lean_array_set(x_11, x_779, x_982);
x_984 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_984, 0, x_10);
lean_ctor_set(x_984, 1, x_983);
if (lean_is_scalar(x_980)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_980;
}
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_979);
return x_985;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_972);
lean_dec(x_11);
lean_dec(x_10);
x_986 = lean_ctor_get(x_977, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_977, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_977)) {
 lean_ctor_release(x_977, 0);
 lean_ctor_release(x_977, 1);
 x_988 = x_977;
} else {
 lean_dec_ref(x_977);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
}
else
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_784);
lean_dec(x_11);
lean_dec(x_10);
x_990 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_991 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_990, x_1, x_2, x_796, x_4, x_5, x_6, x_7, x_8, x_783);
lean_dec(x_1);
return x_991;
}
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; uint8_t x_1021; uint8_t x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
x_992 = lean_ctor_get(x_7, 0);
x_993 = lean_ctor_get(x_7, 1);
x_994 = lean_ctor_get(x_7, 2);
x_995 = lean_ctor_get(x_7, 3);
x_996 = lean_ctor_get(x_7, 4);
x_997 = lean_ctor_get(x_7, 5);
x_998 = lean_ctor_get(x_7, 6);
x_999 = lean_ctor_get(x_7, 7);
lean_inc(x_999);
lean_inc(x_998);
lean_inc(x_997);
lean_inc(x_996);
lean_inc(x_995);
lean_inc(x_994);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_7);
x_1000 = l_Lean_replaceRef(x_1, x_995);
lean_dec(x_995);
x_1001 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_1001, 0, x_992);
lean_ctor_set(x_1001, 1, x_993);
lean_ctor_set(x_1001, 2, x_994);
lean_ctor_set(x_1001, 3, x_1000);
lean_ctor_set(x_1001, 4, x_996);
lean_ctor_set(x_1001, 5, x_997);
lean_ctor_set(x_1001, 6, x_998);
lean_ctor_set(x_1001, 7, x_999);
x_1002 = lean_st_ref_take(x_8, x_9);
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1002, 1);
lean_inc(x_1004);
lean_dec(x_1002);
x_1005 = lean_ctor_get(x_1003, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1003, 1);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1003, 2);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1003, 3);
lean_inc(x_1008);
if (lean_is_exclusive(x_1003)) {
 lean_ctor_release(x_1003, 0);
 lean_ctor_release(x_1003, 1);
 lean_ctor_release(x_1003, 2);
 lean_ctor_release(x_1003, 3);
 x_1009 = x_1003;
} else {
 lean_dec_ref(x_1003);
 x_1009 = lean_box(0);
}
x_1010 = lean_unsigned_to_nat(1u);
x_1011 = lean_nat_add(x_1006, x_1010);
if (lean_is_scalar(x_1009)) {
 x_1012 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1012 = x_1009;
}
lean_ctor_set(x_1012, 0, x_1005);
lean_ctor_set(x_1012, 1, x_1011);
lean_ctor_set(x_1012, 2, x_1007);
lean_ctor_set(x_1012, 3, x_1008);
x_1013 = lean_st_ref_set(x_8, x_1012, x_1004);
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
x_1016 = lean_ctor_get(x_3, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_3, 1);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_3, 2);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_3, 3);
lean_inc(x_1019);
x_1020 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_1021 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_1022 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
x_1023 = lean_ctor_get(x_3, 5);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_3, 6);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_3, 7);
lean_inc(x_1025);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_1026 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1026 = lean_box(0);
}
if (lean_is_scalar(x_1026)) {
 x_1027 = lean_alloc_ctor(0, 8, 3);
} else {
 x_1027 = x_1026;
}
lean_ctor_set(x_1027, 0, x_1016);
lean_ctor_set(x_1027, 1, x_1017);
lean_ctor_set(x_1027, 2, x_1018);
lean_ctor_set(x_1027, 3, x_1019);
lean_ctor_set(x_1027, 4, x_1006);
lean_ctor_set(x_1027, 5, x_1023);
lean_ctor_set(x_1027, 6, x_1024);
lean_ctor_set(x_1027, 7, x_1025);
lean_ctor_set_uint8(x_1027, sizeof(void*)*8, x_1020);
lean_ctor_set_uint8(x_1027, sizeof(void*)*8 + 1, x_1021);
lean_ctor_set_uint8(x_1027, sizeof(void*)*8 + 2, x_1022);
if (x_14 == 0)
{
lean_object* x_1028; uint8_t x_1029; 
x_1028 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_1029 = lean_name_eq(x_10, x_1028);
if (x_1029 == 0)
{
lean_object* x_1030; uint8_t x_1031; 
x_1030 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__2;
x_1031 = lean_name_eq(x_10, x_1030);
if (x_1031 == 0)
{
lean_object* x_1032; uint8_t x_1033; 
x_1032 = l_myMacro____x40_Init_Notation___hyg_12938____closed__13;
x_1033 = lean_name_eq(x_10, x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; uint8_t x_1035; 
x_1034 = l_myMacro____x40_Init_Notation___hyg_12336____closed__8;
x_1035 = lean_name_eq(x_10, x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; uint8_t x_1037; 
lean_dec(x_11);
x_1036 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_1037 = lean_name_eq(x_10, x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; uint8_t x_1039; 
x_1038 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_1039 = lean_name_eq(x_10, x_1038);
if (x_1039 == 0)
{
lean_object* x_1040; uint8_t x_1041; 
x_1040 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_1041 = lean_name_eq(x_10, x_1040);
if (x_1041 == 0)
{
lean_object* x_1042; uint8_t x_1043; 
x_1042 = l_Lean_strLitKind;
x_1043 = lean_name_eq(x_10, x_1042);
if (x_1043 == 0)
{
lean_object* x_1044; uint8_t x_1045; 
x_1044 = l_Lean_numLitKind;
x_1045 = lean_name_eq(x_10, x_1044);
if (x_1045 == 0)
{
lean_object* x_1046; uint8_t x_1047; 
x_1046 = l_Lean_scientificLitKind;
x_1047 = lean_name_eq(x_10, x_1046);
if (x_1047 == 0)
{
lean_object* x_1048; uint8_t x_1049; 
x_1048 = l_Lean_charLitKind;
x_1049 = lean_name_eq(x_10, x_1048);
if (x_1049 == 0)
{
lean_object* x_1050; uint8_t x_1051; 
lean_dec(x_1015);
x_1050 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_1051 = lean_name_eq(x_10, x_1050);
if (x_1051 == 0)
{
lean_object* x_1052; uint8_t x_1053; 
lean_dec(x_1);
x_1052 = l_Lean_choiceKind;
x_1053 = lean_name_eq(x_10, x_1052);
lean_dec(x_10);
if (x_1053 == 0)
{
lean_object* x_1054; 
x_1054 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
lean_dec(x_8);
lean_dec(x_1001);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1027);
lean_dec(x_2);
return x_1054;
}
else
{
lean_object* x_1055; lean_object* x_1056; 
x_1055 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_1056 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_1055, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
lean_dec(x_8);
lean_dec(x_1001);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1027);
lean_dec(x_2);
return x_1056;
}
}
else
{
lean_object* x_1057; 
lean_dec(x_10);
lean_dec(x_2);
x_1057 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
lean_dec(x_8);
lean_dec(x_1001);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_1057;
}
}
else
{
lean_object* x_1058; 
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1015)) {
 x_1058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1058 = x_1015;
}
lean_ctor_set(x_1058, 0, x_1);
lean_ctor_set(x_1058, 1, x_1014);
return x_1058;
}
}
else
{
lean_object* x_1059; 
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1015)) {
 x_1059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1059 = x_1015;
}
lean_ctor_set(x_1059, 0, x_1);
lean_ctor_set(x_1059, 1, x_1014);
return x_1059;
}
}
else
{
lean_object* x_1060; 
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1015)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_1015;
}
lean_ctor_set(x_1060, 0, x_1);
lean_ctor_set(x_1060, 1, x_1014);
return x_1060;
}
}
else
{
lean_object* x_1061; 
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1015)) {
 x_1061 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1061 = x_1015;
}
lean_ctor_set(x_1061, 0, x_1);
lean_ctor_set(x_1061, 1, x_1014);
return x_1061;
}
}
else
{
lean_object* x_1062; 
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1015)) {
 x_1062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1062 = x_1015;
}
lean_ctor_set(x_1062, 0, x_1);
lean_ctor_set(x_1062, 1, x_1014);
return x_1062;
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1015);
lean_dec(x_10);
x_1063 = lean_unsigned_to_nat(0u);
x_1064 = l_Lean_Syntax_getArg(x_1, x_1063);
lean_inc(x_1001);
lean_inc(x_1064);
x_1065 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1064, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1066 = lean_ctor_get(x_1065, 1);
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = lean_unsigned_to_nat(2u);
x_1068 = l_Lean_Syntax_getArg(x_1, x_1067);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1069 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1069 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_1001);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1027);
x_1070 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1068, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1066);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
lean_dec(x_1070);
x_1073 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_1001, x_8, x_1072);
x_1074 = lean_ctor_get(x_1073, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1073, 1);
lean_inc(x_1075);
lean_dec(x_1073);
x_1076 = l_Lean_Elab_Term_getCurrMacroScope(x_1027, x_4, x_5, x_6, x_1001, x_8, x_1075);
lean_dec(x_1001);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1027);
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1076, 1);
lean_inc(x_1078);
lean_dec(x_1076);
x_1079 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1078);
lean_dec(x_8);
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1079, 1);
lean_inc(x_1081);
if (lean_is_exclusive(x_1079)) {
 lean_ctor_release(x_1079, 0);
 lean_ctor_release(x_1079, 1);
 x_1082 = x_1079;
} else {
 lean_dec_ref(x_1079);
 x_1082 = lean_box(0);
}
x_1083 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_1084 = l_Lean_addMacroScope(x_1080, x_1083, x_1077);
x_1085 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_1086 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_1087 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1087, 0, x_1074);
lean_ctor_set(x_1087, 1, x_1085);
lean_ctor_set(x_1087, 2, x_1084);
lean_ctor_set(x_1087, 3, x_1086);
x_1088 = l_Array_empty___closed__1;
x_1089 = lean_array_push(x_1088, x_1087);
x_1090 = lean_array_push(x_1088, x_1064);
x_1091 = lean_array_push(x_1090, x_1071);
x_1092 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_1069)) {
 x_1093 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1093 = x_1069;
}
lean_ctor_set(x_1093, 0, x_1092);
lean_ctor_set(x_1093, 1, x_1091);
x_1094 = lean_array_push(x_1089, x_1093);
x_1095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1095, 0, x_12);
lean_ctor_set(x_1095, 1, x_1094);
if (lean_is_scalar(x_1082)) {
 x_1096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1096 = x_1082;
}
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1081);
return x_1096;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_1069);
lean_dec(x_1064);
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1097 = lean_ctor_get(x_1070, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1070, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1099 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1099 = lean_box(0);
}
if (lean_is_scalar(x_1099)) {
 x_1100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1100 = x_1099;
}
lean_ctor_set(x_1100, 0, x_1097);
lean_ctor_set(x_1100, 1, x_1098);
return x_1100;
}
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_1064);
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1101 = lean_ctor_get(x_1065, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1065, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_1065)) {
 lean_ctor_release(x_1065, 0);
 lean_ctor_release(x_1065, 1);
 x_1103 = x_1065;
} else {
 lean_dec_ref(x_1065);
 x_1103 = lean_box(0);
}
if (lean_is_scalar(x_1103)) {
 x_1104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1104 = x_1103;
}
lean_ctor_set(x_1104, 0, x_1101);
lean_ctor_set(x_1104, 1, x_1102);
return x_1104;
}
}
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1015);
lean_dec(x_10);
x_1105 = lean_unsigned_to_nat(0u);
x_1106 = l_Lean_Syntax_getArg(x_1, x_1105);
lean_dec(x_1);
x_1107 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1108 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1107, x_1106, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
return x_1108;
}
}
else
{
lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
x_1109 = l_Lean_instInhabitedSyntax;
x_1110 = lean_array_get(x_1109, x_11, x_1010);
x_1111 = l_Lean_Syntax_isNone(x_1110);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; uint8_t x_1116; 
lean_dec(x_1015);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1112 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1112 = lean_box(0);
}
x_1113 = lean_unsigned_to_nat(0u);
x_1114 = l_Lean_Syntax_getArg(x_1110, x_1113);
x_1115 = l_Lean_Syntax_getArg(x_1110, x_1010);
x_1116 = l_Lean_Syntax_isNone(x_1115);
if (x_1116 == 0)
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; uint8_t x_1120; 
x_1117 = l_Lean_Syntax_getArg(x_1115, x_1113);
lean_inc(x_1117);
x_1118 = l_Lean_Syntax_getKind(x_1117);
x_1119 = l_myMacro____x40_Init_Notation___hyg_13855____closed__8;
x_1120 = lean_name_eq(x_1118, x_1119);
lean_dec(x_1118);
if (x_1120 == 0)
{
lean_object* x_1121; 
lean_inc(x_8);
lean_inc(x_1001);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1027);
lean_inc(x_2);
x_1121 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1114, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = l_Lean_Syntax_setArg(x_1110, x_1113, x_1122);
x_1125 = l_Lean_Syntax_getArg(x_1117, x_1010);
x_1126 = l_Lean_Syntax_getArgs(x_1125);
lean_dec(x_1125);
x_1127 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1128 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1126, x_1127, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1123);
lean_dec(x_1126);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1131 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1131 = lean_box(0);
}
x_1132 = l_Lean_nullKind;
if (lean_is_scalar(x_1112)) {
 x_1133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1133 = x_1112;
}
lean_ctor_set(x_1133, 0, x_1132);
lean_ctor_set(x_1133, 1, x_1129);
x_1134 = l_Lean_Syntax_setArg(x_1117, x_1010, x_1133);
x_1135 = l_Lean_Syntax_setArg(x_1115, x_1113, x_1134);
x_1136 = l_Lean_Syntax_setArg(x_1124, x_1010, x_1135);
x_1137 = lean_array_set(x_11, x_1010, x_1136);
x_1138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1138, 0, x_10);
lean_ctor_set(x_1138, 1, x_1137);
if (lean_is_scalar(x_1131)) {
 x_1139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1139 = x_1131;
}
lean_ctor_set(x_1139, 0, x_1138);
lean_ctor_set(x_1139, 1, x_1130);
return x_1139;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec(x_1124);
lean_dec(x_1117);
lean_dec(x_1115);
lean_dec(x_1112);
lean_dec(x_11);
lean_dec(x_10);
x_1140 = lean_ctor_get(x_1128, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1128, 1);
lean_inc(x_1141);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1142 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1142 = lean_box(0);
}
if (lean_is_scalar(x_1142)) {
 x_1143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1143 = x_1142;
}
lean_ctor_set(x_1143, 0, x_1140);
lean_ctor_set(x_1143, 1, x_1141);
return x_1143;
}
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_1117);
lean_dec(x_1115);
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1144 = lean_ctor_get(x_1121, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1121, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 x_1146 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1147 = x_1146;
}
lean_ctor_set(x_1147, 0, x_1144);
lean_ctor_set(x_1147, 1, x_1145);
return x_1147;
}
}
else
{
lean_object* x_1148; 
lean_dec(x_1117);
lean_dec(x_1115);
x_1148 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1114, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
if (lean_is_exclusive(x_1148)) {
 lean_ctor_release(x_1148, 0);
 lean_ctor_release(x_1148, 1);
 x_1151 = x_1148;
} else {
 lean_dec_ref(x_1148);
 x_1151 = lean_box(0);
}
x_1152 = l_Lean_Syntax_setArg(x_1110, x_1113, x_1149);
x_1153 = lean_array_set(x_11, x_1010, x_1152);
if (lean_is_scalar(x_1112)) {
 x_1154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1154 = x_1112;
}
lean_ctor_set(x_1154, 0, x_10);
lean_ctor_set(x_1154, 1, x_1153);
if (lean_is_scalar(x_1151)) {
 x_1155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1155 = x_1151;
}
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_1150);
return x_1155;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_11);
lean_dec(x_10);
x_1156 = lean_ctor_get(x_1148, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1148, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1148)) {
 lean_ctor_release(x_1148, 0);
 lean_ctor_release(x_1148, 1);
 x_1158 = x_1148;
} else {
 lean_dec_ref(x_1148);
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
else
{
lean_object* x_1160; 
lean_dec(x_1115);
x_1160 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1114, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
if (lean_obj_tag(x_1160) == 0)
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1161 = lean_ctor_get(x_1160, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1160, 1);
lean_inc(x_1162);
if (lean_is_exclusive(x_1160)) {
 lean_ctor_release(x_1160, 0);
 lean_ctor_release(x_1160, 1);
 x_1163 = x_1160;
} else {
 lean_dec_ref(x_1160);
 x_1163 = lean_box(0);
}
x_1164 = l_Lean_Syntax_setArg(x_1110, x_1113, x_1161);
x_1165 = lean_array_set(x_11, x_1010, x_1164);
if (lean_is_scalar(x_1112)) {
 x_1166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1166 = x_1112;
}
lean_ctor_set(x_1166, 0, x_10);
lean_ctor_set(x_1166, 1, x_1165);
if (lean_is_scalar(x_1163)) {
 x_1167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1167 = x_1163;
}
lean_ctor_set(x_1167, 0, x_1166);
lean_ctor_set(x_1167, 1, x_1162);
return x_1167;
}
else
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_11);
lean_dec(x_10);
x_1168 = lean_ctor_get(x_1160, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1160, 1);
lean_inc(x_1169);
if (lean_is_exclusive(x_1160)) {
 lean_ctor_release(x_1160, 0);
 lean_ctor_release(x_1160, 1);
 x_1170 = x_1160;
} else {
 lean_dec_ref(x_1160);
 x_1170 = lean_box(0);
}
if (lean_is_scalar(x_1170)) {
 x_1171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1171 = x_1170;
}
lean_ctor_set(x_1171, 0, x_1168);
lean_ctor_set(x_1171, 1, x_1169);
return x_1171;
}
}
}
else
{
lean_object* x_1172; 
lean_dec(x_1110);
lean_dec(x_1027);
lean_dec(x_1001);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1015)) {
 x_1172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1172 = x_1015;
}
lean_ctor_set(x_1172, 0, x_1);
lean_ctor_set(x_1172, 1, x_1014);
return x_1172;
}
}
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
lean_dec(x_1027);
lean_dec(x_1015);
lean_dec(x_1001);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1173 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_1014);
x_1174 = lean_ctor_get(x_1173, 0);
lean_inc(x_1174);
x_1175 = lean_ctor_get(x_1173, 1);
lean_inc(x_1175);
lean_dec(x_1173);
x_1176 = lean_st_ref_get(x_8, x_1175);
lean_dec(x_8);
x_1177 = lean_ctor_get(x_1176, 1);
lean_inc(x_1177);
lean_dec(x_1176);
x_1178 = lean_st_ref_take(x_2, x_1177);
x_1179 = lean_ctor_get(x_1178, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1178, 1);
lean_inc(x_1180);
lean_dec(x_1178);
x_1181 = lean_ctor_get(x_1179, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1179, 1);
lean_inc(x_1182);
if (lean_is_exclusive(x_1179)) {
 lean_ctor_release(x_1179, 0);
 lean_ctor_release(x_1179, 1);
 x_1183 = x_1179;
} else {
 lean_dec_ref(x_1179);
 x_1183 = lean_box(0);
}
x_1184 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_1174);
x_1185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1185, 0, x_1184);
x_1186 = lean_array_push(x_1182, x_1185);
if (lean_is_scalar(x_1183)) {
 x_1187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1187 = x_1183;
}
lean_ctor_set(x_1187, 0, x_1181);
lean_ctor_set(x_1187, 1, x_1186);
x_1188 = lean_st_ref_set(x_2, x_1187, x_1180);
lean_dec(x_2);
x_1189 = lean_ctor_get(x_1188, 1);
lean_inc(x_1189);
if (lean_is_exclusive(x_1188)) {
 lean_ctor_release(x_1188, 0);
 lean_ctor_release(x_1188, 1);
 x_1190 = x_1188;
} else {
 lean_dec_ref(x_1188);
 x_1190 = lean_box(0);
}
if (lean_is_scalar(x_1190)) {
 x_1191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1191 = x_1190;
}
lean_ctor_set(x_1191, 0, x_1174);
lean_ctor_set(x_1191, 1, x_1189);
return x_1191;
}
}
else
{
lean_object* x_1192; lean_object* x_1193; uint8_t x_1194; 
lean_dec(x_1015);
lean_dec(x_1);
x_1192 = l_Lean_instInhabitedSyntax;
x_1193 = lean_array_get(x_1192, x_11, x_1010);
x_1194 = l_Lean_Syntax_isNone(x_1193);
if (x_1194 == 0)
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_11);
lean_dec(x_10);
x_1195 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_1196 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_1193, x_1195, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1027);
lean_dec(x_2);
lean_dec(x_1193);
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1196, 1);
lean_inc(x_1198);
if (lean_is_exclusive(x_1196)) {
 lean_ctor_release(x_1196, 0);
 lean_ctor_release(x_1196, 1);
 x_1199 = x_1196;
} else {
 lean_dec_ref(x_1196);
 x_1199 = lean_box(0);
}
if (lean_is_scalar(x_1199)) {
 x_1200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1200 = x_1199;
}
lean_ctor_set(x_1200, 0, x_1197);
lean_ctor_set(x_1200, 1, x_1198);
return x_1200;
}
else
{
lean_object* x_1201; lean_object* x_1202; 
lean_dec(x_1193);
x_1201 = lean_box(0);
x_1202 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_1201, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
return x_1202;
}
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1015);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1203 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1203 = lean_box(0);
}
x_1204 = l_Lean_instInhabitedSyntax;
x_1205 = lean_array_get(x_1204, x_11, x_1010);
x_1206 = l_Lean_Syntax_getArgs(x_1205);
lean_dec(x_1205);
x_1207 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1208 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1206, x_1207, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
lean_dec(x_1206);
if (lean_obj_tag(x_1208) == 0)
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1208, 1);
lean_inc(x_1210);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1211 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1211 = lean_box(0);
}
x_1212 = l_Lean_nullKind;
if (lean_is_scalar(x_1203)) {
 x_1213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1213 = x_1203;
}
lean_ctor_set(x_1213, 0, x_1212);
lean_ctor_set(x_1213, 1, x_1209);
x_1214 = lean_array_set(x_11, x_1010, x_1213);
x_1215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1215, 0, x_10);
lean_ctor_set(x_1215, 1, x_1214);
if (lean_is_scalar(x_1211)) {
 x_1216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1216 = x_1211;
}
lean_ctor_set(x_1216, 0, x_1215);
lean_ctor_set(x_1216, 1, x_1210);
return x_1216;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_1203);
lean_dec(x_11);
lean_dec(x_10);
x_1217 = lean_ctor_get(x_1208, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1208, 1);
lean_inc(x_1218);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1219 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1219 = lean_box(0);
}
if (lean_is_scalar(x_1219)) {
 x_1220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1220 = x_1219;
}
lean_ctor_set(x_1220, 0, x_1217);
lean_ctor_set(x_1220, 1, x_1218);
return x_1220;
}
}
}
else
{
lean_object* x_1221; lean_object* x_1222; 
lean_dec(x_1015);
lean_dec(x_11);
lean_dec(x_10);
x_1221 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1222 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_1221, x_1, x_2, x_1027, x_4, x_5, x_6, x_1001, x_8, x_1014);
lean_dec(x_1);
return x_1222;
}
}
}
}
case 3:
{
lean_object* x_1226; lean_object* x_1227; 
x_1226 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1227 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(x_1226, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1227;
}
default: 
{
lean_object* x_1228; 
lean_dec(x_1);
x_1228 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1228;
}
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("collecting variables at pattern: ");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
x_54 = lean_st_ref_get(x_10, x_11);
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
x_61 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_62 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Elab_Term_CollectPatternVars_collect(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_2 + x_24;
x_26 = x_22;
x_27 = lean_array_uset(x_17, x_2, x_26);
x_2 = x_25;
x_3 = x_27;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_34 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_KernelException_toMessageData___closed__15;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_39 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_38, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_41 = l_Lean_Elab_Term_CollectPatternVars_collect(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 1;
x_45 = x_2 + x_44;
x_46 = x_42;
x_47 = lean_array_uset(x_17, x_2, x_46);
x_2 = x_45;
x_3 = x_47;
x_11 = x_43;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = x_12;
x_17 = lean_box_usize(x_15);
x_18 = l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1;
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed), 11, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
x_20 = x_19;
x_21 = lean_apply_8(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_34 = lean_array_get_size(x_32);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = x_32;
x_37 = lean_box_usize(x_35);
x_38 = l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1;
x_39 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed), 11, 3);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
lean_closure_set(x_39, 2, x_36);
x_40 = x_39;
x_41 = lean_apply_8(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_33);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_31);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_13);
x_15 = l_Lean_Elab_Term_CollectPatternVars_main(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
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
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
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
lean_object* x_9; lean_object* x_10; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = lean_st_ref_get(x_7, x_8);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_6, 3);
lean_inc(x_38);
x_39 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 2);
lean_inc(x_43);
x_44 = lean_st_ref_get(x_7, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_37);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_48, 0, x_37);
x_49 = x_48;
x_50 = lean_environment_main_module(x_37);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_38);
x_52 = l_Lean_expandMacros(x_1, x_51, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_7, x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_56, 1);
lean_dec(x_59);
lean_ctor_set(x_56, 1, x_54);
x_60 = lean_st_ref_set(x_7, x_56, x_57);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_9 = x_53;
x_10 = x_61;
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 2);
x_64 = lean_ctor_get(x_56, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_st_ref_set(x_7, x_65, x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_9 = x_53;
x_10 = x_67;
goto block_33;
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
lean_dec(x_52);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_69, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_69);
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
lean_object* x_78; uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__5___rarg(x_46);
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
}
block_33:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_15);
x_17 = l_Lean_Elab_Term_CollectPatternVars_collect(x_9, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_7, x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_24);
return x_25;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3___rarg), 1, 0);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
x_34 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_10, 2);
lean_inc(x_38);
x_39 = lean_st_ref_get(x_11, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_32);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_43, 0, x_32);
x_44 = x_43;
x_45 = lean_environment_main_module(x_32);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_38);
lean_ctor_set(x_46, 5, x_33);
x_47 = l_Lean_expandMacros(x_28, x_46, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_take(x_11, x_41);
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
x_55 = lean_st_ref_set(x_11, x_51, x_52);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_13 = x_48;
x_14 = x_56;
goto block_25;
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
x_61 = lean_st_ref_set(x_11, x_60, x_52);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_13 = x_48;
x_14 = x_62;
goto block_25;
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
x_68 = l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1(x_64, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3___rarg(x_41);
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
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_st_ref_get(x_7, x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
lean_inc(x_7);
lean_inc(x_16);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__4(x_1, x_10, x_11, x_18, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_7, x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_16, x_22);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_7);
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
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_getPatternsVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_3 == x_4;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_9(x_1, x_5, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
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
lean_dec(x_1);
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
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
lean_object* l_Array_foldlMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_le(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_usize_of_nat(x_4);
x_19 = lean_usize_of_nat(x_5);
x_20 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__3(x_1, x_3, x_18, x_19, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
}
}
}
lean_object* l_Array_forM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l_Array_forM___at_Lean_Meta_ToHide_fixpointStep___spec__4___lambda__1___boxed), 10, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_box(0);
x_14 = l_Array_foldlMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_mkFVar(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_inferType(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_mkFreshExprMVarWithId(x_9, x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
return x_30;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed), 8, 0);
return x_1;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_array_get_size(x_4);
x_15 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___closed__1;
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Array_forM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(x_15, x_4, x_16, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
x_24 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 0;
x_27 = lean_box(0);
lean_inc(x_7);
x_28 = l_Lean_Meta_mkFreshTypeMVar(x_26, x_27, x_7, x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed), 12, 4);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_4);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_2);
x_32 = 0;
x_33 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_25, x_32, x_29, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = 0;
x_36 = lean_box(0);
lean_inc(x_7);
x_37 = l_Lean_Meta_mkFreshTypeMVar(x_35, x_36, x_7, x_8, x_9, x_10, x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_5);
x_40 = l_Lean_Elab_Term_mkFreshBinderName(x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__3___boxed), 13, 5);
lean_closure_set(x_43, 0, x_3);
lean_closure_set(x_43, 1, x_34);
lean_closure_set(x_43, 2, x_4);
lean_closure_set(x_43, 3, x_1);
lean_closure_set(x_43, 4, x_2);
x_44 = 0;
x_45 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_41, x_44, x_38, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
return x_45;
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Array_foldlMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_forM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg), 2, 0);
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
x_25 = l_Lean_Meta_whnf(x_23, x_7, x_8, x_9, x_10, x_11);
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
x_45 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
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
x_56 = l_Lean_Meta_whnf(x_54, x_7, x_8, x_9, x_10, x_11);
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
x_77 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_75);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: mvarId: ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fvar: ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_mkMVar(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_instantiateMVars(x_24, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_95; lean_object* x_96; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_115 = lean_st_ref_get(x_10, x_27);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = 0;
x_95 = x_120;
x_96 = x_119;
goto block_114;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_dec(x_115);
x_122 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_123 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_122, x_5, x_6, x_7, x_8, x_9, x_10, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_unbox(x_124);
lean_dec(x_124);
x_95 = x_126;
x_96 = x_125;
goto block_114;
}
block_94:
{
if (lean_obj_tag(x_26) == 2)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_23);
x_30 = l_Lean_mkFVar(x_23);
lean_inc(x_30);
lean_inc(x_29);
x_79 = l_Lean_Meta_assignExprMVar(x_29, x_30, x_7, x_8, x_9, x_10, x_28);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_get(x_10, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = 0;
x_31 = x_86;
x_32 = x_85;
goto block_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_89 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_88, x_5, x_6, x_7, x_8, x_9, x_10, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_31 = x_92;
x_32 = x_91;
goto block_78;
}
block_78:
{
if (x_31 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_7);
x_33 = l_Lean_Meta_getLocalDecl(x_23, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Meta_instantiateLocalDeclMVars(x_34, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = l_Lean_mkMVar(x_29);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_30);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_KernelException_toMessageData___closed__15;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_60 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_59, x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_7);
x_62 = l_Lean_Meta_getLocalDecl(x_23, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_Meta_instantiateLocalDeclMVars(x_63, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_array_push(x_4, x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_12 = x_69;
x_13 = x_67;
goto block_18;
}
else
{
uint8_t x_70; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_62);
if (x_74 == 0)
{
return x_62;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_62);
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
lean_object* x_93; 
lean_dec(x_26);
lean_dec(x_23);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_4);
x_12 = x_93;
x_13 = x_28;
goto block_18;
}
}
block_114:
{
if (x_95 == 0)
{
lean_dec(x_22);
x_28 = x_96;
goto block_94;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_97 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_97, 0, x_22);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_26);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_26);
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_23);
x_106 = l_Lean_mkFVar(x_23);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_KernelException_toMessageData___closed__15;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_112 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_111, x_110, x_5, x_6, x_7, x_8, x_9, x_10, x_96);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_28 = x_113;
goto block_94;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_25);
if (x_127 == 0)
{
return x_25;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_25, 0);
x_129 = lean_ctor_get(x_25, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_25);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_21, 0);
lean_inc(x_131);
lean_dec(x_21);
lean_inc(x_7);
x_132 = l_Lean_Meta_getLocalDecl(x_131, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_135 = l_Lean_Meta_instantiateLocalDeclMVars(x_133, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_array_push(x_4, x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_12 = x_139;
x_13 = x_137;
goto block_18;
}
else
{
uint8_t x_140; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_140 = !lean_is_exclusive(x_135);
if (x_140 == 0)
{
return x_135;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_135, 0);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_135);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_144 = !lean_is_exclusive(x_132);
if (x_144 == 0)
{
return x_132;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_132, 0);
x_146 = lean_ctor_get(x_132, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_132);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
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
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_NameSet_contains(x_15, x_1);
lean_dec(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_NameSet_contains(x_20, x_1);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_NameSet_insert___closed__1;
x_18 = lean_box(0);
x_19 = l_Std_RBNode_insert___rarg(x_17, x_16, x_1, x_18);
lean_ctor_set(x_13, 0, x_19);
x_20 = lean_st_ref_set(x_2, x_13, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_28 = l_Lean_NameSet_insert___closed__1;
x_29 = lean_box(0);
x_30 = l_Std_RBNode_insert___rarg(x_28, x_25, x_1, x_29);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
x_32 = lean_st_ref_set(x_2, x_31, x_14);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_33);
return x_35;
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
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
x_13 = l_Lean_KernelException_toMessageData___closed__15;
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
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg___boxed), 2, 0);
return x_7;
}
}
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_LocalDecl_type(x_2);
x_4 = l_Lean_Expr_occurs(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Expr_mvarId_x21(x_1);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_getExprMVarAssignment_x3f(x_10, x_5, x_6, x_7, x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg(x_8, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_21 = l_Lean_Meta_inferType(x_1, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_19);
x_24 = l_Lean_mkFVar(x_19);
x_25 = l_Lean_Meta_assignExprMVar(x_10, x_24, x_5, x_6, x_7, x_8, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Elab_Term_mkFreshBinderName(x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = 0;
lean_inc(x_19);
x_32 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
x_33 = lean_st_ref_get(x_8, x_29);
lean_dec(x_8);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_take(x_2, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_41, 0, x_1);
x_42 = lean_array_get_size(x_39);
lean_inc(x_39);
x_43 = l_Array_findIdx_x3f_loop___rarg(x_39, x_41, x_42, x_30, lean_box(0));
lean_dec(x_42);
x_44 = l_Lean_NameSet_insert___closed__1;
x_45 = lean_box(0);
lean_inc(x_19);
x_46 = l_Std_RBNode_insert___rarg(x_44, x_40, x_19, x_45);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_array_push(x_39, x_32);
lean_ctor_set(x_36, 2, x_46);
lean_ctor_set(x_36, 1, x_47);
x_48 = lean_st_ref_set(x_2, x_36, x_37);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_19);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
lean_dec(x_43);
x_56 = l_Array_insertAt___rarg(x_39, x_55, x_32);
lean_dec(x_55);
lean_ctor_set(x_36, 2, x_46);
lean_ctor_set(x_36, 1, x_56);
x_57 = lean_st_ref_set(x_2, x_36, x_37);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_19);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_36, 0);
x_65 = lean_ctor_get(x_36, 1);
x_66 = lean_ctor_get(x_36, 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_36);
x_67 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_67, 0, x_1);
x_68 = lean_array_get_size(x_65);
lean_inc(x_65);
x_69 = l_Array_findIdx_x3f_loop___rarg(x_65, x_67, x_68, x_30, lean_box(0));
lean_dec(x_68);
x_70 = l_Lean_NameSet_insert___closed__1;
x_71 = lean_box(0);
lean_inc(x_19);
x_72 = l_Std_RBNode_insert___rarg(x_70, x_66, x_19, x_71);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_array_push(x_65, x_32);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = lean_st_ref_set(x_2, x_74, x_37);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_19);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
lean_dec(x_69);
x_81 = l_Array_insertAt___rarg(x_65, x_80, x_32);
lean_dec(x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_64);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_72);
x_83 = lean_st_ref_set(x_2, x_82, x_37);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_19);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
return x_21;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_21, 0);
x_90 = lean_ctor_get(x_21, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_15, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_16, 0);
lean_inc(x_94);
lean_dec(x_16);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_15, 0, x_95);
return x_15;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_15, 1);
lean_inc(x_96);
lean_dec(x_15);
x_97 = lean_ctor_get(x_16, 0);
lean_inc(x_97);
lean_dec(x_16);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
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
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ToDepElimPattern_main_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Elab_Term_ToDepElimPattern_main(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_2 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_2, x_24);
x_2 = x_23;
x_3 = x_25;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_37 = l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
static lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc(x_2);
x_15 = l_Array_extract___rarg(x_2, x_14, x_13);
x_16 = lean_array_get_size(x_2);
x_17 = l_Array_extract___rarg(x_2, x_13, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = x_17;
x_21 = lean_box_usize(x_19);
x_22 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1;
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1___boxed), 11, 3);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_20);
x_24 = x_23;
x_25 = lean_apply_8(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_array_to_list(lean_box(0), x_15);
x_31 = lean_array_to_list(lean_box(0), x_28);
x_32 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_array_to_list(lean_box(0), x_15);
x_37 = lean_array_to_list(lean_box(0), x_33);
x_38 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_inaccessible_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Expr_arrayLit_x3f(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_1, x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isNatLit(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Expr_isStringLit(x_1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_isCharLit(x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_isFVar(x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isMVar(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = l_Lean_Meta_whnf(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_expr_eqv(x_21, x_1);
if (x_23 == 0)
{
lean_dec(x_1);
x_1 = x_21;
x_9 = x_22;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_21);
x_25 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_8, x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_find(x_31, x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_27);
x_33 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 6)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux(x_1, x_36);
x_38 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
lean_inc(x_1);
x_42 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_39, x_41);
x_43 = lean_array_get_size(x_42);
x_44 = lean_ctor_get(x_35, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 4);
lean_inc(x_45);
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
x_47 = lean_nat_dec_eq(x_43, x_46);
lean_dec(x_46);
lean_dec(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_42);
lean_dec(x_35);
lean_dec(x_27);
x_48 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(x_35, x_42, x_27, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_27);
x_55 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_25);
x_56 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_56;
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
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
x_61 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_62 = l_Lean_Expr_fvarId_x21(x_1);
x_63 = lean_st_ref_get(x_8, x_9);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_2, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_62);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1___boxed), 2, 1);
lean_closure_set(x_69, 0, x_62);
x_70 = lean_array_get_size(x_68);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_69, x_68, x_71, x_70);
lean_dec(x_70);
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_dec(x_62);
x_73 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(0);
x_79 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(x_62, x_1, x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_1);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_9);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_9);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_1);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_9);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Expr_getAppNumArgsAux(x_1, x_86);
x_88 = lean_unsigned_to_nat(2u);
x_89 = l_Lean_Expr_getArg_x21(x_1, x_88, x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_90 = l_Lean_Elab_Term_ToDepElimPattern_main(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_unsigned_to_nat(1u);
x_95 = l_Lean_Expr_getArg_x21(x_1, x_94, x_87);
lean_dec(x_87);
lean_dec(x_1);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
lean_ctor_set(x_90, 0, x_97);
return x_90;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_95);
lean_free_object(x_90);
lean_dec(x_92);
x_98 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
x_99 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_93);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_90, 0);
x_101 = lean_ctor_get(x_90, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_90);
x_102 = lean_unsigned_to_nat(1u);
x_103 = l_Lean_Expr_getArg_x21(x_1, x_102, x_87);
lean_dec(x_87);
lean_dec(x_1);
if (lean_obj_tag(x_103) == 1)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_103);
lean_dec(x_100);
x_107 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
x_108 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_90);
if (x_109 == 0)
{
return x_90;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_90, 0);
x_111 = lean_ctor_get(x_90, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_90);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_113 = lean_ctor_get(x_11, 0);
lean_inc(x_113);
lean_dec(x_11);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_116, 0, x_119);
return x_116;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_116, 0);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_116);
x_122 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_114);
x_124 = !lean_is_exclusive(x_116);
if (x_124 == 0)
{
return x_116;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_116, 0);
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_116);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_1);
x_128 = lean_ctor_get(x_10, 0);
lean_inc(x_128);
lean_dec(x_10);
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_st_ref_get(x_8, x_9);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_get(x_2, x_131);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_ctor_get(x_132, 1);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_129);
x_137 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1___boxed), 2, 1);
lean_closure_set(x_137, 0, x_129);
x_138 = lean_array_get_size(x_136);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_137, x_136, x_139, x_138);
lean_dec(x_138);
lean_dec(x_136);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_128);
lean_ctor_set(x_132, 0, x_141);
return x_132;
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_free_object(x_132);
x_142 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_135);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_146, 0);
lean_dec(x_148);
x_149 = l_Lean_Expr_fvarId_x21(x_128);
lean_dec(x_128);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_146, 0, x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = l_Lean_Expr_fvarId_x21(x_128);
lean_dec(x_128);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_142);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_142, 0);
lean_dec(x_156);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_128);
lean_ctor_set(x_142, 0, x_157);
return x_142;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
lean_dec(x_142);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_128);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_161 = lean_ctor_get(x_132, 0);
x_162 = lean_ctor_get(x_132, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_132);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_129);
x_164 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___lambda__1___boxed), 2, 1);
lean_closure_set(x_164, 0, x_129);
x_165 = lean_array_get_size(x_163);
x_166 = lean_unsigned_to_nat(0u);
x_167 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_164, x_163, x_166, x_165);
lean_dec(x_165);
lean_dec(x_163);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_128);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_162);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
x_177 = l_Lean_Expr_fvarId_x21(x_128);
lean_dec(x_128);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_128);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_128);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_9);
return x_185;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Elab_Term_ToDepElimPattern_main(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_2 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_2, x_24);
x_2 = x_23;
x_3 = x_25;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_instantiateLocalDeclMVars(x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_2 + x_21;
x_23 = x_19;
x_24 = lean_array_uset(x_16, x_2, x_23);
x_2 = x_22;
x_3 = x_24;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_LocalDecl_fvarId(x_2);
x_4 = lean_local_ctx_erase(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDepElimPatterns___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LocalContext_addDecl), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = x_2;
x_14 = lean_box_usize(x_12);
x_15 = l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1;
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed), 11, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_13);
x_17 = l_Lean_NameSet_empty;
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_st_ref_get(x_9, x_10);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_mk_ref(x_18, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = x_16;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_22);
x_25 = lean_apply_8(x_24, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_9, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_22, x_29);
lean_dec(x_22);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_get_size(x_33);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = x_33;
x_37 = lean_box_usize(x_35);
x_38 = l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1;
x_39 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed), 10, 3);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
lean_closure_set(x_39, 2, x_36);
x_40 = x_39;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_41 = lean_apply_7(x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_6, 1);
x_46 = lean_array_get_size(x_42);
x_47 = l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1;
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_47, x_45, x_42, x_48, x_46);
x_50 = l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2;
x_51 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_50, x_49, x_42, x_48, x_46);
lean_dec(x_46);
lean_ctor_set(x_6, 1, x_51);
x_52 = lean_apply_9(x_3, x_42, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_6, 0);
x_54 = lean_ctor_get(x_6, 1);
x_55 = lean_ctor_get(x_6, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_6);
x_56 = lean_array_get_size(x_42);
x_57 = l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1;
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_57, x_54, x_42, x_58, x_56);
x_60 = l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2;
x_61 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_60, x_59, x_42, x_58, x_56);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_55);
x_63 = lean_apply_9(x_3, x_42, x_26, x_4, x_5, x_62, x_7, x_8, x_9, x_43);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_41);
if (x_64 == 0)
{
return x_41;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_41, 0);
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_41);
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
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_25);
if (x_68 == 0)
{
return x_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_25);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_withDepElimPatterns___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_instantiateMVars(x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_2 + x_21;
x_23 = x_19;
x_24 = lean_array_uset(x_16, x_2, x_23);
x_2 = x_22;
x_3 = x_24;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_to_list(lean_box(0), x_4);
x_14 = lean_array_to_list(lean_box(0), x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_apply_9(x_2, x_15, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___boxed), 9, 2);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
x_14 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_withSynthesize___rarg(x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Elab_Term_finalizePatternDecls(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_18);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = x_18;
x_26 = lean_box_usize(x_24);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1;
x_28 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed), 10, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_25);
x_29 = x_28;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = lean_apply_7(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1), 12, 3);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_5);
lean_closure_set(x_33, 2, x_19);
x_34 = l_Lean_Elab_Term_withDepElimPatterns___rarg(x_21, x_31, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
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
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep(x_7, x_6);
x_9 = l_Lean_Elab_Term_instToStringPatternVar___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__2(lean_object* x_1) {
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
x_6 = l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_5);
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
x_11 = l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_10);
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
x_35 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
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
x_18 = l_Lean_KernelException_toMessageData___closed__15;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = l_List_redLength___rarg(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
x_22 = l_List_toArrayAux___rarg(x_19, x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = x_22;
x_27 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_24, x_25, x_26);
x_28 = x_27;
x_29 = l_Array_isEmpty___rarg(x_28);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; 
x_30 = 0;
lean_inc(x_7);
x_31 = l_Lean_Meta_mkLambdaFVars(x_28, x_17, x_30, x_15, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_3, x_2, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_28);
x_39 = l_Lean_mkSimpleThunk(x_17);
x_40 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_3, x_2, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 3, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
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
x_37 = lean_st_ref_get(x_8, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = 0;
x_19 = x_42;
x_20 = x_41;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_19 = x_48;
x_20 = x_47;
goto block_36;
}
block_36:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_2);
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_17, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_17);
x_24 = lean_array_to_list(lean_box(0), x_17);
x_25 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_24);
x_26 = l_Lean_MessageData_ofList(x_25);
lean_dec(x_25);
x_27 = l_Lean_Elab_Term_elabMatchAltView___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_KernelException_toMessageData___closed__15;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_32 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_31, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_34, 0, x_18);
lean_closure_set(x_34, 1, x_31);
lean_closure_set(x_34, 2, x_2);
x_35 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_17, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
x_55 = lean_ctor_get(x_7, 2);
x_56 = lean_ctor_get(x_7, 3);
x_57 = lean_ctor_get(x_7, 4);
x_58 = lean_ctor_get(x_7, 5);
x_59 = lean_ctor_get(x_7, 6);
x_60 = lean_ctor_get(x_7, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_61 = l_Lean_replaceRef(x_10, x_56);
lean_dec(x_56);
lean_dec(x_10);
x_62 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_59);
lean_ctor_set(x_62, 7, x_60);
lean_inc(x_8);
lean_inc(x_62);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_63 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_62, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_86 = lean_st_ref_get(x_8, x_65);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 3);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get_uint8(x_88, sizeof(void*)*1);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = 0;
x_68 = x_91;
x_69 = x_90;
goto block_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_93 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_94 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_93, x_3, x_4, x_5, x_6, x_62, x_8, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_68 = x_97;
x_69 = x_96;
goto block_85;
}
block_85:
{
if (x_68 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_71 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_71, 0, x_67);
lean_closure_set(x_71, 1, x_70);
lean_closure_set(x_71, 2, x_2);
x_72 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_66, x_71, x_3, x_4, x_5, x_6, x_62, x_8, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_66);
x_73 = lean_array_to_list(lean_box(0), x_66);
x_74 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_73);
x_75 = l_Lean_MessageData_ofList(x_74);
lean_dec(x_74);
x_76 = l_Lean_Elab_Term_elabMatchAltView___closed__2;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_KernelException_toMessageData___closed__15;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_81 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_80, x_79, x_3, x_4, x_5, x_6, x_62, x_8, x_69);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed), 11, 3);
lean_closure_set(x_83, 0, x_67);
lean_closure_set(x_83, 1, x_80);
lean_closure_set(x_83, 2, x_2);
x_84 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(x_66, x_83, x_3, x_4, x_5, x_6, x_62, x_8, x_82);
return x_84;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_62);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_63, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_100 = x_63;
} else {
 lean_dec_ref(x_63);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
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
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_12938____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ignoreUnusedAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if true, do not generate error if an alternative is not used");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__3;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__5;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("redundant alternative");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__1;
x_15 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_3, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_apply_9(x_14, x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_2 = x_13;
x_3 = x_26;
x_10 = x_25;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_8, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_8, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_8, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_8, 7);
lean_inc(x_40);
x_41 = l_Lean_replaceRef(x_32, x_36);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set(x_42, 7, x_40);
x_43 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__4;
x_44 = 2;
x_45 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_43, x_44, x_4, x_5, x_6, x_7, x_42, x_9, x_10);
lean_dec(x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = lean_apply_9(x_14, x_3, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_2 = x_13;
x_3 = x_57;
x_10 = x_56;
goto _start;
}
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_48);
if (x_59 == 0)
{
return x_48;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = l_Lean_Elab_Term_match_ignoreUnusedAlts;
x_13 = l_Lean_Option_get___at_Lean_Elab_addMacroStack___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 2);
x_15 = l_List_isEmpty___rarg(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_14, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
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
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
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
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = l_List_isEmpty___rarg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_counterExamplesToMessageData(x_10);
x_13 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_KernelException_toMessageData___closed__15;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 7);
lean_inc(x_24);
x_25 = l_Lean_Syntax_getHead_x3f___closed__1;
x_26 = l_Lean_Syntax_getHead_x3f___closed__2;
x_27 = l_Lean_Syntax_getHead_x3f___closed__3;
x_28 = l_Lean_Syntax_getHead_x3f___closed__4;
lean_inc(x_20);
x_29 = l_Lean_Syntax_getHead_x3f_match__1___rarg(x_20, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_30 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_36 = lean_ctor_get(x_7, 7);
lean_dec(x_36);
x_37 = lean_ctor_get(x_7, 6);
lean_dec(x_37);
x_38 = lean_ctor_get(x_7, 5);
lean_dec(x_38);
x_39 = lean_ctor_get(x_7, 4);
lean_dec(x_39);
x_40 = lean_ctor_get(x_7, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_7, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_7, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
x_45 = l_Lean_replaceRef(x_44, x_20);
lean_dec(x_20);
lean_dec(x_44);
lean_ctor_set(x_7, 3, x_45);
x_46 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_7);
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
lean_dec(x_29);
x_52 = l_Lean_replaceRef(x_51, x_20);
lean_dec(x_20);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_53, 0, x_17);
lean_ctor_set(x_53, 1, x_18);
lean_ctor_set(x_53, 2, x_19);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_21);
lean_ctor_set(x_53, 5, x_22);
lean_ctor_set(x_53, 6, x_23);
lean_ctor_set(x_53, 7, x_24);
x_54 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_16, x_3, x_4, x_5, x_6, x_53, x_8, x_9);
lean_dec(x_8);
lean_dec(x_53);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
x_59 = lean_box(0);
x_60 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(x_2, x_1, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_60;
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_reportMatcherResultErrors(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
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
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_7, 1);
x_20 = lean_ctor_get(x_7, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
x_24 = lean_ctor_get(x_9, 3);
x_25 = lean_ctor_get(x_9, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_10, 1);
x_28 = lean_ctor_get_usize(x_10, 2);
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_11, 1);
x_32 = lean_ctor_get_usize(x_11, 2);
x_33 = lean_ctor_get(x_11, 0);
lean_dec(x_33);
x_34 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_35 = lean_string_dec_eq(x_31, x_34);
lean_dec(x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_27);
lean_free_object(x_9);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_36 = lean_apply_1(x_3, x_1);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_1, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
x_40 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_41 = lean_string_dec_eq(x_27, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_34);
x_42 = lean_apply_1(x_3, x_1);
return x_42;
}
else
{
lean_dec(x_27);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_1);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_43 = lean_box_usize(x_32);
x_44 = lean_box_usize(x_28);
x_45 = lean_apply_6(x_2, x_22, x_23, x_24, x_15, x_43, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_34);
lean_ctor_set(x_10, 1, x_40);
x_46 = lean_apply_1(x_3, x_1);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_34);
lean_ctor_set(x_10, 1, x_40);
x_47 = lean_apply_1(x_3, x_1);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
x_48 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_49 = lean_string_dec_eq(x_27, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_13);
x_51 = lean_apply_1(x_3, x_50);
return x_51;
}
else
{
lean_dec(x_27);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_52 = lean_box_usize(x_32);
x_53 = lean_box_usize(x_28);
x_54 = lean_apply_6(x_2, x_22, x_23, x_24, x_15, x_52, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_34);
lean_ctor_set(x_10, 1, x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_13);
x_56 = lean_apply_1(x_3, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_34);
lean_ctor_set(x_10, 1, x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_13);
x_58 = lean_apply_1(x_3, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_11, 1);
x_60 = lean_ctor_get_usize(x_11, 2);
lean_inc(x_59);
lean_dec(x_11);
x_61 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_62 = lean_string_dec_eq(x_59, x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; 
lean_free_object(x_10);
lean_dec(x_27);
lean_free_object(x_9);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_63 = lean_apply_1(x_3, x_1);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_64 = x_1;
} else {
 lean_dec_ref(x_1);
 x_64 = lean_box(0);
}
x_65 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_66 = lean_string_dec_eq(x_27, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_67 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set_usize(x_67, 2, x_60);
lean_ctor_set(x_10, 0, x_67);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_13);
x_69 = lean_apply_1(x_3, x_68);
return x_69;
}
else
{
lean_dec(x_27);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_70 = lean_box_usize(x_60);
x_71 = lean_box_usize(x_28);
x_72 = lean_apply_6(x_2, x_22, x_23, x_24, x_15, x_70, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_73 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set_usize(x_73, 2, x_60);
lean_ctor_set(x_10, 1, x_65);
lean_ctor_set(x_10, 0, x_73);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_13);
x_75 = lean_apply_1(x_3, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
x_76 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_76, 0, x_12);
lean_ctor_set(x_76, 1, x_61);
lean_ctor_set_usize(x_76, 2, x_60);
lean_ctor_set(x_10, 1, x_65);
lean_ctor_set(x_10, 0, x_76);
if (lean_is_scalar(x_64)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_64;
}
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_13);
x_78 = lean_apply_1(x_3, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_79; size_t x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_10, 1);
x_80 = lean_ctor_get_usize(x_10, 2);
lean_inc(x_79);
lean_dec(x_10);
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
x_82 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_83 = x_11;
} else {
 lean_dec_ref(x_11);
 x_83 = lean_box(0);
}
x_84 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_85 = lean_string_dec_eq(x_81, x_84);
lean_dec(x_81);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_79);
lean_free_object(x_9);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_86 = lean_apply_1(x_3, x_1);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_87 = x_1;
} else {
 lean_dec_ref(x_1);
 x_87 = lean_box(0);
}
x_88 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_89 = lean_string_dec_eq(x_79, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_84);
lean_ctor_set_usize(x_90, 2, x_82);
x_91 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_79);
lean_ctor_set_usize(x_91, 2, x_80);
lean_ctor_set(x_9, 0, x_91);
if (lean_is_scalar(x_87)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_87;
}
lean_ctor_set(x_92, 0, x_5);
lean_ctor_set(x_92, 1, x_13);
x_93 = lean_apply_1(x_3, x_92);
return x_93;
}
else
{
lean_dec(x_79);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_87);
lean_dec(x_83);
lean_free_object(x_9);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_94 = lean_box_usize(x_82);
x_95 = lean_box_usize(x_80);
x_96 = lean_apply_6(x_2, x_22, x_23, x_24, x_15, x_94, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_2);
if (lean_is_scalar(x_83)) {
 x_97 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_97 = x_83;
}
lean_ctor_set(x_97, 0, x_12);
lean_ctor_set(x_97, 1, x_84);
lean_ctor_set_usize(x_97, 2, x_82);
x_98 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_88);
lean_ctor_set_usize(x_98, 2, x_80);
lean_ctor_set(x_9, 0, x_98);
if (lean_is_scalar(x_87)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_87;
}
lean_ctor_set(x_99, 0, x_5);
lean_ctor_set(x_99, 1, x_13);
x_100 = lean_apply_1(x_3, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_2);
if (lean_is_scalar(x_83)) {
 x_101 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_101 = x_83;
}
lean_ctor_set(x_101, 0, x_12);
lean_ctor_set(x_101, 1, x_84);
lean_ctor_set_usize(x_101, 2, x_82);
x_102 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_88);
lean_ctor_set_usize(x_102, 2, x_80);
lean_ctor_set(x_9, 0, x_102);
if (lean_is_scalar(x_87)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_87;
}
lean_ctor_set(x_103, 0, x_5);
lean_ctor_set(x_103, 1, x_13);
x_104 = lean_apply_1(x_3, x_103);
return x_104;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; size_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_105 = lean_ctor_get(x_9, 1);
x_106 = lean_ctor_get(x_9, 2);
x_107 = lean_ctor_get(x_9, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_9);
x_108 = lean_ctor_get(x_10, 1);
lean_inc(x_108);
x_109 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_110 = x_10;
} else {
 lean_dec_ref(x_10);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_11, 1);
lean_inc(x_111);
x_112 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_113 = x_11;
} else {
 lean_dec_ref(x_11);
 x_113 = lean_box(0);
}
x_114 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_115 = lean_string_dec_eq(x_111, x_114);
lean_dec(x_111);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_free_object(x_7);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_116 = lean_apply_1(x_3, x_1);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_117 = x_1;
} else {
 lean_dec_ref(x_1);
 x_117 = lean_box(0);
}
x_118 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_119 = lean_string_dec_eq(x_108, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
if (lean_is_scalar(x_113)) {
 x_120 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_120 = x_113;
}
lean_ctor_set(x_120, 0, x_12);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set_usize(x_120, 2, x_112);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_108);
lean_ctor_set_usize(x_121, 2, x_109);
x_122 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_105);
lean_ctor_set(x_122, 2, x_106);
lean_ctor_set(x_122, 3, x_107);
lean_ctor_set(x_7, 0, x_122);
if (lean_is_scalar(x_117)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_117;
}
lean_ctor_set(x_123, 0, x_5);
lean_ctor_set(x_123, 1, x_13);
x_124 = lean_apply_1(x_3, x_123);
return x_124;
}
else
{
lean_dec(x_108);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_110);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_125 = lean_box_usize(x_112);
x_126 = lean_box_usize(x_109);
x_127 = lean_apply_6(x_2, x_105, x_106, x_107, x_15, x_125, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_2);
if (lean_is_scalar(x_113)) {
 x_128 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_128 = x_113;
}
lean_ctor_set(x_128, 0, x_12);
lean_ctor_set(x_128, 1, x_114);
lean_ctor_set_usize(x_128, 2, x_112);
if (lean_is_scalar(x_110)) {
 x_129 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_129 = x_110;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_118);
lean_ctor_set_usize(x_129, 2, x_109);
x_130 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_105);
lean_ctor_set(x_130, 2, x_106);
lean_ctor_set(x_130, 3, x_107);
lean_ctor_set(x_7, 0, x_130);
if (lean_is_scalar(x_117)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_117;
}
lean_ctor_set(x_131, 0, x_5);
lean_ctor_set(x_131, 1, x_13);
x_132 = lean_apply_1(x_3, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
if (lean_is_scalar(x_113)) {
 x_133 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_133 = x_113;
}
lean_ctor_set(x_133, 0, x_12);
lean_ctor_set(x_133, 1, x_114);
lean_ctor_set_usize(x_133, 2, x_112);
if (lean_is_scalar(x_110)) {
 x_134 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_134 = x_110;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_118);
lean_ctor_set_usize(x_134, 2, x_109);
x_135 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_105);
lean_ctor_set(x_135, 2, x_106);
lean_ctor_set(x_135, 3, x_107);
lean_ctor_set(x_7, 0, x_135);
if (lean_is_scalar(x_117)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_117;
}
lean_ctor_set(x_136, 0, x_5);
lean_ctor_set(x_136, 1, x_13);
x_137 = lean_apply_1(x_3, x_136);
return x_137;
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; size_t x_144; lean_object* x_145; lean_object* x_146; size_t x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_138 = lean_ctor_get(x_7, 1);
lean_inc(x_138);
lean_dec(x_7);
x_139 = lean_ctor_get(x_9, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_9, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_9, 3);
lean_inc(x_141);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_142 = x_9;
} else {
 lean_dec_ref(x_9);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_10, 1);
lean_inc(x_143);
x_144 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_145 = x_10;
} else {
 lean_dec_ref(x_10);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_11, 1);
lean_inc(x_146);
x_147 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_148 = x_11;
} else {
 lean_dec_ref(x_11);
 x_148 = lean_box(0);
}
x_149 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_150 = lean_string_dec_eq(x_146, x_149);
lean_dec(x_146);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_151 = lean_apply_1(x_3, x_1);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_152 = x_1;
} else {
 lean_dec_ref(x_1);
 x_152 = lean_box(0);
}
x_153 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_154 = lean_string_dec_eq(x_143, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
if (lean_is_scalar(x_148)) {
 x_155 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_155 = x_148;
}
lean_ctor_set(x_155, 0, x_12);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set_usize(x_155, 2, x_147);
if (lean_is_scalar(x_145)) {
 x_156 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_156 = x_145;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_143);
lean_ctor_set_usize(x_156, 2, x_144);
if (lean_is_scalar(x_142)) {
 x_157 = lean_alloc_ctor(2, 4, 0);
} else {
 x_157 = x_142;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_139);
lean_ctor_set(x_157, 2, x_140);
lean_ctor_set(x_157, 3, x_141);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_138);
lean_ctor_set(x_5, 2, x_158);
if (lean_is_scalar(x_152)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_152;
}
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_13);
x_160 = lean_apply_1(x_3, x_159);
return x_160;
}
else
{
lean_dec(x_143);
if (lean_obj_tag(x_138) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_152);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_142);
lean_free_object(x_5);
lean_dec(x_3);
x_161 = lean_box_usize(x_147);
x_162 = lean_box_usize(x_144);
x_163 = lean_apply_6(x_2, x_139, x_140, x_141, x_15, x_161, x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_2);
if (lean_is_scalar(x_148)) {
 x_164 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_164 = x_148;
}
lean_ctor_set(x_164, 0, x_12);
lean_ctor_set(x_164, 1, x_149);
lean_ctor_set_usize(x_164, 2, x_147);
if (lean_is_scalar(x_145)) {
 x_165 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_165 = x_145;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_153);
lean_ctor_set_usize(x_165, 2, x_144);
if (lean_is_scalar(x_142)) {
 x_166 = lean_alloc_ctor(2, 4, 0);
} else {
 x_166 = x_142;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_139);
lean_ctor_set(x_166, 2, x_140);
lean_ctor_set(x_166, 3, x_141);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_138);
lean_ctor_set(x_5, 2, x_167);
if (lean_is_scalar(x_152)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_152;
}
lean_ctor_set(x_168, 0, x_5);
lean_ctor_set(x_168, 1, x_13);
x_169 = lean_apply_1(x_3, x_168);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_2);
if (lean_is_scalar(x_148)) {
 x_170 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_170 = x_148;
}
lean_ctor_set(x_170, 0, x_12);
lean_ctor_set(x_170, 1, x_149);
lean_ctor_set_usize(x_170, 2, x_147);
if (lean_is_scalar(x_145)) {
 x_171 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_171 = x_145;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_153);
lean_ctor_set_usize(x_171, 2, x_144);
if (lean_is_scalar(x_142)) {
 x_172 = lean_alloc_ctor(2, 4, 0);
} else {
 x_172 = x_142;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_139);
lean_ctor_set(x_172, 2, x_140);
lean_ctor_set(x_172, 3, x_141);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_138);
lean_ctor_set(x_5, 2, x_173);
if (lean_is_scalar(x_152)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_152;
}
lean_ctor_set(x_174, 0, x_5);
lean_ctor_set(x_174, 1, x_13);
x_175 = lean_apply_1(x_3, x_174);
return x_175;
}
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; size_t x_184; lean_object* x_185; lean_object* x_186; size_t x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_176 = lean_ctor_get(x_5, 0);
lean_inc(x_176);
lean_dec(x_5);
x_177 = lean_ctor_get(x_7, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_178 = x_7;
} else {
 lean_dec_ref(x_7);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_9, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_9, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_9, 3);
lean_inc(x_181);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_182 = x_9;
} else {
 lean_dec_ref(x_9);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_10, 1);
lean_inc(x_183);
x_184 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_185 = x_10;
} else {
 lean_dec_ref(x_10);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_11, 1);
lean_inc(x_186);
x_187 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_188 = x_11;
} else {
 lean_dec_ref(x_11);
 x_188 = lean_box(0);
}
x_189 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_190 = lean_string_dec_eq(x_186, x_189);
lean_dec(x_186);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_13);
lean_dec(x_2);
x_191 = lean_apply_1(x_3, x_1);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_192 = x_1;
} else {
 lean_dec_ref(x_1);
 x_192 = lean_box(0);
}
x_193 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_194 = lean_string_dec_eq(x_183, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_2);
if (lean_is_scalar(x_188)) {
 x_195 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_195 = x_188;
}
lean_ctor_set(x_195, 0, x_12);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set_usize(x_195, 2, x_187);
if (lean_is_scalar(x_185)) {
 x_196 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_196 = x_185;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_183);
lean_ctor_set_usize(x_196, 2, x_184);
if (lean_is_scalar(x_182)) {
 x_197 = lean_alloc_ctor(2, 4, 0);
} else {
 x_197 = x_182;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_179);
lean_ctor_set(x_197, 2, x_180);
lean_ctor_set(x_197, 3, x_181);
if (lean_is_scalar(x_178)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_178;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_177);
x_199 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_199, 0, x_176);
lean_ctor_set(x_199, 1, x_6);
lean_ctor_set(x_199, 2, x_198);
if (lean_is_scalar(x_192)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_192;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_13);
x_201 = lean_apply_1(x_3, x_200);
return x_201;
}
else
{
lean_dec(x_183);
if (lean_obj_tag(x_177) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_192);
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_3);
x_202 = lean_box_usize(x_187);
x_203 = lean_box_usize(x_184);
x_204 = lean_apply_6(x_2, x_179, x_180, x_181, x_176, x_202, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_2);
if (lean_is_scalar(x_188)) {
 x_205 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_205 = x_188;
}
lean_ctor_set(x_205, 0, x_12);
lean_ctor_set(x_205, 1, x_189);
lean_ctor_set_usize(x_205, 2, x_187);
if (lean_is_scalar(x_185)) {
 x_206 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_206 = x_185;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_193);
lean_ctor_set_usize(x_206, 2, x_184);
if (lean_is_scalar(x_182)) {
 x_207 = lean_alloc_ctor(2, 4, 0);
} else {
 x_207 = x_182;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_179);
lean_ctor_set(x_207, 2, x_180);
lean_ctor_set(x_207, 3, x_181);
if (lean_is_scalar(x_178)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_178;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_177);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_176);
lean_ctor_set(x_209, 1, x_6);
lean_ctor_set(x_209, 2, x_208);
if (lean_is_scalar(x_192)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_192;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_13);
x_211 = lean_apply_1(x_3, x_210);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_2);
if (lean_is_scalar(x_188)) {
 x_212 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_212 = x_188;
}
lean_ctor_set(x_212, 0, x_12);
lean_ctor_set(x_212, 1, x_189);
lean_ctor_set_usize(x_212, 2, x_187);
if (lean_is_scalar(x_185)) {
 x_213 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_213 = x_185;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_193);
lean_ctor_set_usize(x_213, 2, x_184);
if (lean_is_scalar(x_182)) {
 x_214 = lean_alloc_ctor(2, 4, 0);
} else {
 x_214 = x_182;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_179);
lean_ctor_set(x_214, 2, x_180);
lean_ctor_set(x_214, 3, x_181);
if (lean_is_scalar(x_178)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_178;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_177);
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_176);
lean_ctor_set(x_216, 1, x_6);
lean_ctor_set(x_216, 2, x_215);
if (lean_is_scalar(x_192)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_192;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_218 = lean_apply_1(x_3, x_217);
return x_218;
}
}
}
}
}
else
{
lean_object* x_219; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_219 = lean_apply_1(x_3, x_1);
return x_219;
}
}
else
{
lean_object* x_220; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_220 = lean_apply_1(x_3, x_1);
return x_220;
}
}
else
{
lean_object* x_221; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_221 = lean_apply_1(x_3, x_1);
return x_221;
}
}
else
{
lean_object* x_222; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_222 = lean_apply_1(x_3, x_1);
return x_222;
}
}
}
else
{
lean_object* x_223; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_223 = lean_apply_1(x_3, x_1);
return x_223;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("altLHSS.length == rhss.size\n  ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__1;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.Match.0.Lean.Elab.Term.isMatchUnit?");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1;
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__3;
x_3 = lean_unsigned_to_nat(725u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthAux___rarg(x_1, x_8);
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__4;
x_14 = lean_panic_fn(x_12, x_13);
x_15 = lean_apply_5(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_18, 1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_20, 1);
x_29 = lean_ctor_get(x_24, 1);
x_30 = lean_ctor_get(x_25, 1);
x_31 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1;
x_32 = lean_string_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_36 = lean_string_dec_eq(x_29, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
else
{
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = lean_array_get(x_39, x_2, x_8);
if (lean_obj_tag(x_40) == 6)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Expr_hasLooseBVars(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_7);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_7);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_7);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_7);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_7);
return x_62;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(x_5);
x_8 = lean_apply_4(x_2, x_3, x_4, x_7, x_6);
return x_8;
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_apply_5(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_13 = x_4;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = x_15;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_elabMatchAltView(x_18, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_3 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_3, x_24);
x_3 = x_23;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid match-expression, type of pattern variable '");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' contains metavariables");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = l_Lean_LocalDecl_toExpr(x_1);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_LocalDecl_type(x_1);
x_17 = l_Lean_indentExpr(x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_KernelException_toMessageData___closed__15;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Term_throwMVarError___rarg(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryPostpone___boxed), 7, 0);
return x_1;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_LocalDecl_hasExprMVar(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___boxed), 9, 1);
lean_closure_set(x_17, 0, x_12);
x_18 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg(x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_2 = x_13;
x_3 = x_22;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid match-expression, pattern contains metavariables");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_10, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_indentExpr(x_12);
x_15 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_KernelException_toMessageData___closed__15;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Term_throwMVarError___rarg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Meta_Match_Pattern_hasExprMVar(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___boxed), 9, 1);
lean_closure_set(x_17, 0, x_12);
x_18 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg(x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_2 = x_13;
x_3 = x_22;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_Match_instantiateAltLHSMVars(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_6, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 7);
lean_inc(x_27);
x_28 = l_Lean_replaceRef(x_18, x_23);
lean_dec(x_23);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
x_30 = lean_box(0);
lean_inc(x_7);
lean_inc(x_29);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_19, 2);
x_31 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(x_19, x_19, x_30, x_2, x_3, x_4, x_5, x_29, x_7, x_17);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(x_19, x_33, x_30, x_2, x_3, x_4, x_5, x_29, x_7, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_16);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_free_object(x_1);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
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
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
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
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_31;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_31, 0);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_Lean_Meta_Match_instantiateAltLHSMVars(x_60, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_6, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_6, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_6, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_6, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_6, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_6, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_6, 7);
lean_inc(x_73);
x_74 = l_Lean_replaceRef(x_64, x_69);
lean_dec(x_69);
lean_dec(x_64);
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_67);
lean_ctor_set(x_75, 2, x_68);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_70);
lean_ctor_set(x_75, 5, x_71);
lean_ctor_set(x_75, 6, x_72);
lean_ctor_set(x_75, 7, x_73);
x_76 = lean_box(0);
lean_inc(x_7);
lean_inc(x_75);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_65, 2);
x_77 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(x_65, x_65, x_76, x_2, x_3, x_4, x_5, x_75, x_7, x_63);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get(x_62, 2);
lean_inc(x_79);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_80 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(x_65, x_79, x_76, x_2, x_3, x_4, x_5, x_75, x_7, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_62);
lean_ctor_set(x_86, 1, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_62);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_94 = x_80;
} else {
 lean_dec_ref(x_80);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_77, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_77, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_98 = x_77;
} else {
 lean_dec_ref(x_77);
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
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_ctor_get(x_61, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_61, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_102 = x_61;
} else {
 lean_dec_ref(x_61);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___rarg), 1, 0);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_95 = lean_st_ref_get(x_7, x_8);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_6, 3);
lean_inc(x_99);
x_100 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_97);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_6, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_6, 2);
lean_inc(x_104);
x_105 = lean_st_ref_get(x_7, x_102);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_98);
x_109 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_109, 0, x_98);
x_110 = x_109;
x_111 = lean_environment_main_module(x_98);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_101);
lean_ctor_set(x_112, 3, x_103);
lean_ctor_set(x_112, 4, x_104);
lean_ctor_set(x_112, 5, x_99);
x_113 = l_Lean_Elab_Term_expandMacrosInPatterns(x_12, x_112, x_108);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_st_ref_take(x_7, x_107);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_117, 1);
lean_dec(x_120);
lean_ctor_set(x_117, 1, x_115);
x_121 = lean_st_ref_set(x_7, x_117, x_118);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_13 = x_114;
x_14 = x_122;
goto block_94;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_117, 0);
x_124 = lean_ctor_get(x_117, 2);
x_125 = lean_ctor_get(x_117, 3);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_117);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_115);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_125);
x_127 = lean_st_ref_set(x_7, x_126, x_118);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_13 = x_114;
x_14 = x_128;
goto block_94;
}
}
else
{
lean_object* x_129; 
lean_dec(x_10);
lean_dec(x_9);
x_129 = lean_ctor_get(x_113, 0);
lean_inc(x_129);
lean_dec(x_113);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7(x_130, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_107);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_130);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
else
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___rarg(x_107);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_139);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
block_94:
{
lean_object* x_15; uint8_t x_71; lean_object* x_72; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_st_ref_get(x_7, x_14);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get_uint8(x_84, sizeof(void*)*1);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = 0;
x_71 = x_87;
x_72 = x_86;
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_90 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_91);
lean_dec(x_91);
x_71 = x_93;
x_72 = x_92;
goto block_81;
}
block_70:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_array_get_size(x_13);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = x_13;
x_20 = lean_box_usize(x_17);
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed__const__1;
lean_inc(x_10);
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1___boxed), 11, 4);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_19);
x_23 = x_22;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_apply_7(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_2, x_3, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_array_get_size(x_25);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
lean_inc(x_25);
x_31 = x_25;
x_32 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(x_30, x_18, x_31);
x_33 = x_32;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Meta_instantiateMVars(x_10, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_to_list(lean_box(0), x_25);
x_38 = l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_box(x_11);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_box(x_11);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_33);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_9);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_33);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_34);
if (x_58 == 0)
{
return x_34;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_34, 0);
x_60 = lean_ctor_get(x_34, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_34);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_27);
if (x_62 == 0)
{
return x_27;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_24);
if (x_66 == 0)
{
return x_24;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_24, 0);
x_68 = lean_ctor_get(x_24, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_24);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
block_81:
{
if (x_71 == 0)
{
x_15 = x_72;
goto block_70;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_10);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_10);
x_74 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__2;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_KernelException_toMessageData___closed__15;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_79 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_78, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_72);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_15 = x_80;
goto block_70;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = 1;
x_12 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1), 8, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__2___boxed), 9, 0);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs___boxed), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_4);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_commitIfDidNotPostpone___rarg(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f(x_25, x_26, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_23);
x_31 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1;
lean_inc(x_5);
x_32 = l_Lean_Elab_Term_mkAuxName(x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
lean_inc(x_30);
lean_inc(x_24);
x_35 = l_Lean_Meta_Match_mkMatcher(x_33, x_24, x_30, x_25, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_24, x_38, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_43 = l_Lean_Elab_Term_reportMatcherResultErrors(x_25, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_25);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
lean_dec(x_36);
x_47 = l_Lean_mkApp(x_46, x_41);
x_48 = l_Lean_mkAppN(x_47, x_23);
lean_dec(x_23);
x_49 = l_Lean_mkAppN(x_48, x_26);
lean_dec(x_26);
x_65 = lean_st_ref_get(x_10, x_44);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = 0;
x_50 = x_70;
x_51 = x_69;
goto block_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_73 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_72, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
x_50 = x_76;
x_51 = x_75;
goto block_64;
}
block_64:
{
if (x_50 == 0)
{
lean_object* x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_45);
lean_inc(x_49);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_49);
x_54 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_KernelException_toMessageData___closed__15;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_59 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_58, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_49);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_43);
if (x_77 == 0)
{
return x_43;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_43, 0);
x_79 = lean_ctor_get(x_43, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_43);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_40);
if (x_81 == 0)
{
return x_40;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_40, 0);
x_83 = lean_ctor_get(x_40, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_40);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_35);
if (x_85 == 0)
{
return x_35;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_35, 0);
x_87 = lean_ctor_get(x_35, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_35);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = !lean_is_exclusive(x_32);
if (x_89 == 0)
{
return x_32;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_32, 0);
x_91 = lean_ctor_get(x_32, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_32);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = !lean_is_exclusive(x_27);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_27, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_28, 0);
lean_inc(x_95);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_95);
return x_27;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
lean_dec(x_27);
x_97 = lean_ctor_get(x_28, 0);
lean_inc(x_97);
lean_dec(x_28);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_99 = !lean_is_exclusive(x_27);
if (x_99 == 0)
{
return x_27;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_27, 0);
x_101 = lean_ctor_get(x_27, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_27);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_15, 1);
lean_inc(x_103);
lean_dec(x_15);
x_104 = lean_ctor_get(x_16, 0);
lean_inc(x_104);
lean_dec(x_16);
x_105 = lean_ctor_get(x_17, 0);
lean_inc(x_105);
lean_dec(x_17);
x_106 = lean_ctor_get(x_18, 0);
lean_inc(x_106);
lean_dec(x_18);
x_107 = lean_ctor_get(x_19, 1);
lean_inc(x_107);
lean_dec(x_19);
x_108 = lean_array_get_size(x_104);
x_109 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1;
lean_inc(x_5);
x_110 = l_Lean_Elab_Term_mkAuxName(x_109, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_106);
lean_inc(x_108);
lean_inc(x_105);
x_113 = l_Lean_Meta_Match_mkMatcher(x_111, x_105, x_108, x_106, x_7, x_8, x_9, x_10, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_108);
x_117 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_118 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_105, x_116, x_117, x_5, x_6, x_7, x_8, x_9, x_10, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_114);
x_121 = l_Lean_Elab_Term_reportMatcherResultErrors(x_106, x_114, x_5, x_6, x_7, x_8, x_9, x_10, x_120);
lean_dec(x_106);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_114, 0);
lean_inc(x_124);
lean_dec(x_114);
x_125 = l_Lean_mkApp(x_124, x_119);
x_126 = l_Lean_mkAppN(x_125, x_104);
lean_dec(x_104);
x_127 = l_Lean_mkAppN(x_126, x_107);
lean_dec(x_107);
x_143 = lean_st_ref_get(x_10, x_122);
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
x_128 = x_148;
x_129 = x_147;
goto block_142;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_143, 1);
lean_inc(x_149);
lean_dec(x_143);
x_150 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_151 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_150, x_5, x_6, x_7, x_8, x_9, x_10, x_149);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_152);
lean_dec(x_152);
x_128 = x_154;
x_129 = x_153;
goto block_142;
}
block_142:
{
if (x_128 == 0)
{
lean_object* x_130; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_123;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_123);
lean_inc(x_127);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_127);
x_132 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_KernelException_toMessageData___closed__15;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_137 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_136, x_135, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_137, 0);
lean_dec(x_139);
lean_ctor_set(x_137, 0, x_127);
return x_137;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_127);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_119);
lean_dec(x_114);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_155 = !lean_is_exclusive(x_121);
if (x_155 == 0)
{
return x_121;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_121, 0);
x_157 = lean_ctor_get(x_121, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_121);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_114);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_159 = !lean_is_exclusive(x_118);
if (x_159 == 0)
{
return x_118;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_118, 0);
x_161 = lean_ctor_get(x_118, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_118);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_163 = !lean_is_exclusive(x_113);
if (x_163 == 0)
{
return x_113;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_113, 0);
x_165 = lean_ctor_get(x_113, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_113);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_110);
if (x_167 == 0)
{
return x_110;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_110, 0);
x_169 = lean_ctor_get(x_110, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_110);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_171 = !lean_is_exclusive(x_15);
if (x_171 == 0)
{
return x_15;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_15, 0);
x_173 = lean_ctor_get(x_15, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_15);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_setArg(x_1, x_18, x_2);
x_20 = lean_array_push(x_3, x_19);
lean_inc(x_13);
lean_inc(x_11);
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(x_4, x_5, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(x_15, x_16, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_11, x_12, x_13, x_14, x_15, x_16, x_26);
lean_dec(x_13);
lean_dec(x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_16, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_myMacro____x40_Init_Notation___hyg_14424____closed__1;
lean_inc(x_25);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Array_empty___closed__1;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_Lean_addMacroScope(x_32, x_6, x_28);
lean_inc(x_25);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_7);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_8);
x_39 = lean_array_push(x_35, x_38);
x_40 = l_myMacro____x40_Init_Notation___hyg_1398____closed__8;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_array_push(x_41, x_40);
x_43 = l_myMacro____x40_Init_Notation___hyg_14424____closed__11;
lean_inc(x_25);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_42, x_44);
x_46 = lean_array_push(x_45, x_9);
x_47 = l_myMacro____x40_Init_Notation___hyg_14424____closed__6;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_35, x_48);
x_50 = l_myMacro____x40_Init_Notation___hyg_14424____closed__4;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_36, x_51);
x_53 = l_myMacro____x40_Init_Notation___hyg_14424____closed__12;
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_25);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_35, x_54);
x_56 = l_Lean_nullKind___closed__2;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_52, x_57);
x_59 = lean_array_push(x_58, x_22);
x_60 = l_myMacro____x40_Init_Notation___hyg_14424____closed__2;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_30, 0, x_61);
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_62 = lean_ctor_get(x_30, 0);
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_30);
x_64 = l_myMacro____x40_Init_Notation___hyg_14424____closed__1;
lean_inc(x_25);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_25);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_empty___closed__1;
x_67 = lean_array_push(x_66, x_65);
x_68 = l_Lean_addMacroScope(x_62, x_6, x_28);
lean_inc(x_25);
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_25);
lean_ctor_set(x_69, 1, x_7);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_8);
x_70 = lean_array_push(x_66, x_69);
x_71 = l_myMacro____x40_Init_Notation___hyg_1398____closed__8;
x_72 = lean_array_push(x_70, x_71);
x_73 = lean_array_push(x_72, x_71);
x_74 = l_myMacro____x40_Init_Notation___hyg_14424____closed__11;
lean_inc(x_25);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_25);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_73, x_75);
x_77 = lean_array_push(x_76, x_9);
x_78 = l_myMacro____x40_Init_Notation___hyg_14424____closed__6;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_push(x_66, x_79);
x_81 = l_myMacro____x40_Init_Notation___hyg_14424____closed__4;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_array_push(x_67, x_82);
x_84 = l_myMacro____x40_Init_Notation___hyg_14424____closed__12;
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_25);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_push(x_66, x_85);
x_87 = l_Lean_nullKind___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_array_push(x_83, x_88);
x_90 = lean_array_push(x_89, x_22);
x_91 = l_myMacro____x40_Init_Notation___hyg_14424____closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_63);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = !lean_is_exclusive(x_21);
if (x_94 == 0)
{
return x_21;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_21, 0);
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_21);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_isAuxDiscrName___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_isAuxDiscrName___closed__1;
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
x_11 = l_term_x5b___x5d___closed__5;
x_12 = l_Lean_mkAtomFrom(x_1, x_11);
x_13 = l_Lean_Syntax_mkSep(x_3, x_12);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_33 = lean_ctor_get(x_4, 4);
lean_dec(x_33);
lean_ctor_set(x_4, 4, x_28);
x_34 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(x_8, x_9, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Term_isAuxDiscrName___closed__2;
x_44 = l_Lean_addMacroScope(x_41, x_43, x_38);
x_45 = lean_box(0);
x_46 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
x_48 = l_Lean_Syntax_getId(x_47);
x_49 = l_Lean_Elab_Term_isAuxDiscrName(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_47);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_50 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_51 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_6);
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
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_47, x_3, x_1, x_18, x_43, x_46, x_45, x_20, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
x_60 = lean_ctor_get(x_4, 2);
x_61 = lean_ctor_get(x_4, 3);
x_62 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_65 = lean_ctor_get(x_4, 5);
x_66 = lean_ctor_get(x_4, 6);
x_67 = lean_ctor_get(x_4, 7);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_4);
x_68 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_28);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*8, x_62);
lean_ctor_set_uint8(x_68, sizeof(void*)*8 + 1, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*8 + 2, x_64);
x_69 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(x_8, x_9, x_31);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Term_getCurrMacroScope(x_68, x_5, x_6, x_7, x_8, x_9, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_isAuxDiscrName___closed__2;
x_79 = l_Lean_addMacroScope(x_76, x_78, x_73);
x_80 = lean_box(0);
x_81 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
x_83 = l_Lean_Syntax_getId(x_82);
x_84 = l_Lean_Elab_Term_isAuxDiscrName(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_85 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_86 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_85, x_68, x_5, x_6, x_7, x_8, x_9, x_77);
lean_dec(x_6);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(0);
x_92 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_82, x_3, x_1, x_18, x_78, x_81, x_80, x_20, x_91, x_68, x_5, x_6, x_7, x_8, x_9, x_77);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_93 = lean_ctor_get(x_25, 0);
x_94 = lean_ctor_get(x_25, 1);
x_95 = lean_ctor_get(x_25, 2);
x_96 = lean_ctor_get(x_25, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_25);
x_97 = lean_nat_add(x_94, x_19);
x_98 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_96);
x_99 = lean_st_ref_set(x_9, x_98, x_26);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_4, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_4, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_4, 3);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_106 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_107 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_108 = lean_ctor_get(x_4, 5);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 6);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 7);
lean_inc(x_110);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 x_111 = x_4;
} else {
 lean_dec_ref(x_4);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 8, 3);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_102);
lean_ctor_set(x_112, 2, x_103);
lean_ctor_set(x_112, 3, x_104);
lean_ctor_set(x_112, 4, x_94);
lean_ctor_set(x_112, 5, x_108);
lean_ctor_set(x_112, 6, x_109);
lean_ctor_set(x_112, 7, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*8, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*8 + 1, x_106);
lean_ctor_set_uint8(x_112, sizeof(void*)*8 + 2, x_107);
x_113 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__3___rarg(x_8, x_9, x_100);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Elab_Term_getCurrMacroScope(x_112, x_5, x_6, x_7, x_8, x_9, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Elab_Term_isAuxDiscrName___closed__2;
x_123 = l_Lean_addMacroScope(x_120, x_122, x_117);
x_124 = lean_box(0);
x_125 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_126 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_126, 0, x_114);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_123);
lean_ctor_set(x_126, 3, x_124);
x_127 = l_Lean_Syntax_getId(x_126);
x_128 = l_Lean_Elab_Term_isAuxDiscrName(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_126);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_129 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_130 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_129, x_112, x_5, x_6, x_7, x_8, x_9, x_121);
lean_dec(x_6);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
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
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_box(0);
x_136 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_126, x_3, x_1, x_18, x_122, x_125, x_124, x_20, x_135, x_112, x_5, x_6, x_7, x_8, x_9, x_121);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_22);
lean_dec(x_20);
x_137 = lean_ctor_get(x_21, 1);
lean_inc(x_137);
lean_dec(x_21);
x_138 = lean_array_push(x_3, x_17);
x_2 = x_18;
x_3 = x_138;
x_10 = x_137;
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
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
return x_18;
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 == x_4;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_8(x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
}
lean_object* l_Array_anyMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_4);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_2);
x_17 = lean_nat_dec_le(x_4, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_3);
x_22 = lean_usize_of_nat(x_4);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__3(x_1, x_2, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
}
}
lean_object* l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___lambda__1), 9, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_array_get_size(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_anyMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__2(x_12, x_2, x_14, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_Term_isLocalIdent_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___lambda__1___boxed), 8, 0);
return x_1;
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_15 = lean_array_get_size(x_14);
x_16 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___closed__1;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(x_16, x_14, x_17, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_array_to_list(lean_box(0), x_14);
x_23 = l_Array_empty___closed__1;
x_24 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(x_1, x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
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
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_18, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_18, 0, x_38);
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__3(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Array_anyMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyMUnsafe___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_allM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
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
x_13 = l_Lean_Meta_mkFreshTypeMVar(x_11, x_12, x_4, x_5, x_6, x_7, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
x_28 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_21, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
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
x_35 = l_Lean_Meta_inferType(x_34, x_7, x_8, x_9, x_10, x_33);
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
x_74 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_75 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_74, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l_Lean_Elab_Term_tryPostponeIfMVar(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
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
x_50 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_36);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_36);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_KernelException_toMessageData___closed__15;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_57 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_56, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_59 = l_Lean_Elab_Term_tryPostponeIfMVar(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
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
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
x_16 = l_Lean_Meta_mkFreshTypeMVar(x_14, x_15, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = x_13;
x_18 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_5198____spec__3(x_15, x_16, x_17);
x_19 = x_18;
lean_inc(x_1);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(x_1);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(x_19, x_20, x_22, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isIdent(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getId(x_1);
x_5 = lean_erase_macro_scopes(x_4);
x_6 = l_Lean_Name_isAtomic(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
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
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_7, x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_environment_find(x_26, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_29 = lean_box(x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
if (lean_obj_tag(x_30) == 6)
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_1);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
uint8_t x_33; lean_object* x_34; 
lean_dec(x_30);
x_33 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_34 = lean_box(x_33);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_environment_find(x_37, x_22);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
if (lean_obj_tag(x_42) == 6)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_1);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
x_46 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_36);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
lean_dec(x_50);
x_51 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_52 = lean_box(x_51);
lean_ctor_set(x_10, 0, x_52);
return x_10;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
lean_dec(x_10);
x_54 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar_isAtomicIdent(x_1);
lean_dec(x_1);
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_elabMatchDefault_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
uint8_t l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match expected type should not be provided when discriminants with equality proofs are used");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_get_size(x_13);
x_18 = l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__1;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_anyMUnsafe___at_Array_any___spec__1___rarg(x_18, x_13, x_19, x_17);
lean_dec(x_17);
lean_dec(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__4;
x_23 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_15, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_15);
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
else
{
lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_13);
x_28 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
lean_inc(x_30);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_2);
x_32 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabMatch_elabMatchDefault___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_myMacro____x40_Init_Notation___hyg_12938____closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Syntax_getArgs(x_14);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_14, x_22);
lean_dec(x_14);
x_24 = l_myMacro____x40_Init_Notation___hyg_12938____closed__4;
lean_inc(x_23);
x_25 = l_Lean_Syntax_isOfKind(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Syntax_getArg(x_23, x_22);
lean_inc(x_27);
x_28 = l_Lean_Syntax_isOfKind(x_27, x_15);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_23);
x_29 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Syntax_getArgs(x_27);
lean_dec(x_27);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_nat_dec_eq(x_31, x_22);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_23);
x_33 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_90; 
x_34 = l_Lean_Syntax_getArg(x_23, x_13);
lean_dec(x_23);
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
lean_inc(x_36);
x_90 = l_Lean_Syntax_isOfKind(x_36, x_15);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
x_37 = x_91;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = l_Lean_Syntax_getArgs(x_36);
x_93 = lean_array_get_size(x_92);
lean_dec(x_92);
x_94 = lean_nat_dec_eq(x_93, x_22);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_37 = x_95;
goto block_89;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_36);
x_96 = lean_unsigned_to_nat(4u);
x_97 = l_Lean_Syntax_getArg(x_1, x_96);
x_98 = l_myMacro____x40_Init_Notation___hyg_12938____closed__8;
lean_inc(x_97);
x_99 = l_Lean_Syntax_isOfKind(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_34);
x_100 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_100;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = l_Lean_Syntax_getArg(x_97, x_22);
lean_dec(x_97);
lean_inc(x_101);
x_102 = l_Lean_Syntax_isOfKind(x_101, x_15);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_101);
lean_dec(x_34);
x_103 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = l_Lean_Syntax_getArgs(x_101);
x_105 = lean_array_get_size(x_104);
lean_dec(x_104);
x_106 = lean_nat_dec_eq(x_105, x_13);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_34);
x_107 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = l_Lean_Syntax_getArg(x_101, x_22);
lean_dec(x_101);
x_109 = l_myMacro____x40_Init_Notation___hyg_12938____closed__10;
lean_inc(x_108);
x_110 = l_Lean_Syntax_isOfKind(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_108);
lean_dec(x_34);
x_111 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_111;
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Syntax_getArg(x_108, x_13);
lean_inc(x_112);
x_113 = l_Lean_Syntax_isOfKind(x_112, x_15);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_34);
x_114 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = l_Lean_Syntax_getArgs(x_112);
x_116 = lean_array_get_size(x_115);
lean_dec(x_115);
x_117 = lean_nat_dec_eq(x_116, x_13);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_34);
x_118 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = l_Lean_Syntax_getArg(x_112, x_22);
lean_dec(x_112);
x_120 = l_Lean_identKind___closed__2;
lean_inc(x_119);
x_121 = l_Lean_Syntax_isOfKind(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_119);
lean_dec(x_108);
lean_dec(x_34);
x_122 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_unsigned_to_nat(3u);
x_124 = l_Lean_Syntax_getArg(x_108, x_123);
lean_dec(x_108);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_119);
x_125 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar(x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_34);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_128);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_dec(x_125);
x_131 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(x_1, x_34, x_119, x_124, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_130);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_124);
lean_dec(x_119);
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_125);
if (x_132 == 0)
{
return x_125;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_125, 0);
x_134 = lean_ctor_get(x_125, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_125);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
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
block_89:
{
uint8_t x_38; 
lean_dec(x_37);
lean_inc(x_36);
x_38 = l_Lean_Syntax_isOfKind(x_36, x_15);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_34);
x_39 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = l_Lean_Syntax_getArgs(x_36);
x_41 = lean_array_get_size(x_40);
lean_dec(x_40);
x_42 = lean_nat_dec_eq(x_41, x_13);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_34);
x_43 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Syntax_getArg(x_36, x_22);
lean_dec(x_36);
x_45 = l_Lean_expandExplicitBindersAux_loop___closed__4;
lean_inc(x_44);
x_46 = l_Lean_Syntax_isOfKind(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_34);
x_47 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = l_Lean_Syntax_getArg(x_44, x_13);
lean_dec(x_44);
x_49 = lean_unsigned_to_nat(4u);
x_50 = l_Lean_Syntax_getArg(x_1, x_49);
x_51 = l_myMacro____x40_Init_Notation___hyg_12938____closed__8;
lean_inc(x_50);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_34);
x_53 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_53;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Syntax_getArg(x_50, x_22);
lean_dec(x_50);
lean_inc(x_54);
x_55 = l_Lean_Syntax_isOfKind(x_54, x_15);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_34);
x_56 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_Syntax_getArgs(x_54);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_nat_dec_eq(x_58, x_13);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_34);
x_60 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = l_Lean_Syntax_getArg(x_54, x_22);
lean_dec(x_54);
x_62 = l_myMacro____x40_Init_Notation___hyg_12938____closed__10;
lean_inc(x_61);
x_63 = l_Lean_Syntax_isOfKind(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_48);
lean_dec(x_34);
x_64 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Syntax_getArg(x_61, x_13);
lean_inc(x_65);
x_66 = l_Lean_Syntax_isOfKind(x_65, x_15);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_48);
lean_dec(x_34);
x_67 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_Syntax_getArgs(x_65);
x_69 = lean_array_get_size(x_68);
lean_dec(x_68);
x_70 = lean_nat_dec_eq(x_69, x_13);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_48);
lean_dec(x_34);
x_71 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_Syntax_getArg(x_65, x_22);
lean_dec(x_65);
x_73 = l_Lean_identKind___closed__2;
lean_inc(x_72);
x_74 = l_Lean_Syntax_isOfKind(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_61);
lean_dec(x_48);
lean_dec(x_34);
x_75 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_unsigned_to_nat(3u);
x_77 = l_Lean_Syntax_getArg(x_61, x_76);
lean_dec(x_61);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_72);
x_78 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isPatternVar(x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_48);
lean_dec(x_34);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lean_Elab_Term_elabMatch_elabMatchDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(x_1, x_34, x_72, x_48, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_48);
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_78);
if (x_85 == 0)
{
return x_78;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_78, 0);
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_78);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
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
x_3 = l_myMacro____x40_Init_Notation___hyg_12938____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_8841_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNoMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkApp___closed__1;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_nomatch___elambda__1___closed__2;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_elabNoMatch___closed__1;
x_19 = lean_array_push(x_18, x_14);
x_20 = l_myMacro____x40_Init_Notation___hyg_12938____closed__4;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_mkOptionalNode___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Array_empty___closed__1;
x_25 = l_Lean_mkOptionalNode___closed__1;
x_26 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(x_23, x_24, x_25, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
x_3 = l_Lean_Parser_Term_nomatch___elambda__1___closed__2;
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
lean_object* initialize_Lean_Parser_Term(lean_object*);
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
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_instInhabitedMatchAltView___closed__1 = _init_l_Lean_Elab_Term_instInhabitedMatchAltView___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedMatchAltView___closed__1);
l_Lean_Elab_Term_instInhabitedMatchAltView = _init_l_Lean_Elab_Term_instInhabitedMatchAltView();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedMatchAltView);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__6);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___closed__7);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__2);
l_Lean_Elab_Term_isAuxDiscrName___closed__1 = _init_l_Lean_Elab_Term_isAuxDiscrName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_isAuxDiscrName___closed__1);
l_Lean_Elab_Term_isAuxDiscrName___closed__2 = _init_l_Lean_Elab_Term_isAuxDiscrName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_isAuxDiscrName___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed__const__1);
l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1 = _init_l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1);
l_Lean_Elab_Term_instToStringPatternVar___closed__1 = _init_l_Lean_Elab_Term_instToStringPatternVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instToStringPatternVar___closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601____closed__2);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1601_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1);
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
l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext);
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
l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1 = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1);
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
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1);
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
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2);
l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1 = _init_l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6);
l_Lean_Elab_Term_ToDepElimPattern_State_found___default = _init_l_Lean_Elab_Term_ToDepElimPattern_State_found___default();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_State_found___default);
l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default = _init_l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2);
l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1);
l_Lean_Elab_Term_ToDepElimPattern_main___closed__1 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___closed__1);
l_Lean_Elab_Term_ToDepElimPattern_main___closed__2 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___closed__2);
l_Lean_Elab_Term_ToDepElimPattern_main___closed__3 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___closed__3);
l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1 = _init_l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__1);
l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2 = _init_l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withDepElimPatterns___rarg___closed__2);
l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1 = _init_l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2);
l_Lean_Elab_Term_elabMatchAltView___closed__1 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__1);
l_Lean_Elab_Term_elabMatchAltView___closed__2 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__3);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__4 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__4);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__5 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105____closed__5);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6105_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_match_ignoreUnusedAlts = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_match_ignoreUnusedAlts);
lean_dec_ref(res);
l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__1);
l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__2);
l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__3);
l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1___closed__4);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__1 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__2 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f_match__2___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_isMatchUnit_x3f___closed__4);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__3);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__4 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__4();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___lambda__1___closed__4);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed__const__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed__const__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4);
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
l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2);
l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__1 = _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__1);
l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__2 = _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__2);
l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__3 = _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__3);
l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__4 = _init_l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabMatch_elabMatchDefault___closed__4);
l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_8841_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabNoMatch___closed__1 = _init_l_Lean_Elab_Term_elabNoMatch___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNoMatch___closed__1);
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
