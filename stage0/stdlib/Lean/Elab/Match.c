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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3(lean_object*);
extern lean_object* l_Lean_instToExprName___closed__1;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object*);
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__6;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__2(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed__const__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
extern lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__1;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(size_t, size_t, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_elabMatch_match__12___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop(lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__15___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__4(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns___boxed__const__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__14(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_reportMatcherResultErrors___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__8(lean_object*);
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1202____closed__23;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__6;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed__const__1;
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_ignoreUnusedAlts(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__5(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext___closed__1;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__4;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
lean_object* l_Lean_Elab_Term_elabMatch_match__8___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2(lean_object*);
lean_object* l_List_filterAux___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_elabMatchAltView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__22;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__12;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed(lean_object**);
extern lean_object* l_Lean_rootNamespace___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_instInhabitedContext;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__2;
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__4;
lean_object* l_Lean_Elab_Term_instToStringPatternVar_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___closed__3;
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_861____closed__7;
lean_object* l_Lean_Elab_Term_elabMatch_match__7(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_newArgs___default;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__6;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_getPatternVars_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1;
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__11___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__43;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_nomatch___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__13(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__4(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__4;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_State_found___default;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__11(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__8;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isDone___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__6(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_reportMatcherResultErrors___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSourceInfo___closed__1;
lean_object* l_Lean_Elab_Term_elabMatch_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__4;
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchOptType(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1;
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__13;
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12721____closed__11;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__9(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__2;
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__3(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_870____closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_elabMatchAltView___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__10___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId___boxed(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__5;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3;
lean_object* l_Lean_Elab_Term_elabMatch_match__15(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible_match__1(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(lean_object*, size_t, size_t);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1;
lean_object* l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar___spec__1___closed__1;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addDiscr___closed__1;
lean_object* l_Lean_Elab_Term_instToStringPatternVar(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__16(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__11;
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__10(lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
lean_object* l_Lean_Elab_Term_instToStringPatternVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_State_newLocals___default;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__1(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_scientificLitKind;
extern lean_object* l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__6;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__1;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__13;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed__const__1;
extern lean_object* l_Array_instToStringArray___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__1;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3(lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_261____closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_State_vars___default;
lean_object* l_Lean_Elab_Term_elabMatch_match__7___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__2(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2094____closed__2;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2;
uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__3___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedType_match__1(lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__15;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__6;
uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processImplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__4(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr_match__1(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__3;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___boxed(lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
extern lean_object* l_Lean_Elab_Term_instInhabitedNamedArg;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__9___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_2982____spec__3(size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_regTraceClasses(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__14;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__3;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13348____closed__18;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_tryPostponeIfDiscrTypeIsMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1;
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__46;
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns___spec__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__2;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_main___boxed__const__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__3;
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls_match__1(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3;
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
lean_object* l_Lean_Elab_Term_withDepElimPatterns_match__1(lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__3(lean_object*);
extern lean_object* l_rawNatLit___closed__5;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed__const__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__13___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__4;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
lean_object* l_Lean_Elab_Term_ignoreUnusedAlts___boxed(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch_match__12(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_isNextArgAccessible___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorAppAux_match__1(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538_(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812_(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_paramDeclIdx___default;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
lean_object* l_Lean_Elab_Term_elabMatch_match__16___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabMatch_match__14___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instToStringPatternVar___closed__1;
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_waitExpectedTypeAndDiscrs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS___rarg___boxed__const__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_withElaboratedLHS(lean_object*);
uint8_t l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_ToDepElimPattern_main___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___closed__1;
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__1;
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_matchPatternAttr;
lean_object* l_Lean_Elab_Term_getPatternVars_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__2(lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_19 = l_myMacro____x40_Init_Notation___hyg_1202____closed__23;
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_array_push(x_20, x_19);
x_22 = l_myMacro____x40_Init_Notation___hyg_13348____closed__14;
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_array_push(x_23, x_2);
x_25 = l_myMacro____x40_Init_Notation___hyg_13348____closed__8;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_17, x_26);
x_28 = l_myMacro____x40_Init_Notation___hyg_13348____closed__6;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_myMacro____x40_Init_Notation___hyg_13348____closed__4;
x_31 = lean_array_push(x_30, x_29);
x_32 = l_myMacro____x40_Init_Notation___hyg_13348____closed__18;
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_array_push(x_33, x_4);
x_35 = l_myMacro____x40_Init_Notation___hyg_13348____closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_6, 3);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_6, 3, x_40);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTerm(x_36, x_5, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
x_45 = lean_ctor_get(x_6, 2);
x_46 = lean_ctor_get(x_6, 3);
x_47 = lean_ctor_get(x_6, 4);
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 2);
x_51 = lean_ctor_get(x_6, 5);
lean_inc(x_51);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
lean_inc(x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_36);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_54 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*6 + 1, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*6 + 2, x_50);
x_55 = 1;
x_56 = l_Lean_Elab_Term_elabTerm(x_36, x_5, x_55, x_54, x_7, x_8, x_9, x_10, x_11, x_16);
return x_56;
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
x_20 = l_myMacro____x40_Init_Notation___hyg_1202____closed__23;
x_21 = lean_array_push(x_19, x_20);
x_22 = l_myMacro____x40_Init_Notation___hyg_12721____closed__11;
x_23 = lean_array_push(x_22, x_4);
x_24 = l_Lean_expandExplicitBindersAux_loop___closed__6;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_push(x_18, x_25);
x_27 = l_Lean_nullKind___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_21, x_28);
x_30 = l_myMacro____x40_Init_Notation___hyg_13348____closed__14;
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_array_push(x_31, x_2);
x_33 = l_myMacro____x40_Init_Notation___hyg_13348____closed__8;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_18, x_34);
x_36 = l_myMacro____x40_Init_Notation___hyg_13348____closed__6;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_myMacro____x40_Init_Notation___hyg_13348____closed__4;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_myMacro____x40_Init_Notation___hyg_13348____closed__18;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_array_push(x_41, x_5);
x_43 = l_myMacro____x40_Init_Notation___hyg_13348____closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_7, 3, x_48);
x_49 = 1;
x_50 = l_Lean_Elab_Term_elabTerm(x_44, x_6, x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
x_53 = lean_ctor_get(x_7, 2);
x_54 = lean_ctor_get(x_7, 3);
x_55 = lean_ctor_get(x_7, 4);
x_56 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 1);
x_58 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 2);
x_59 = lean_ctor_get(x_7, 5);
lean_inc(x_59);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
lean_inc(x_44);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_44);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
x_62 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_53);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_55);
lean_ctor_set(x_62, 5, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*6, x_56);
lean_ctor_set_uint8(x_62, sizeof(void*)*6 + 1, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*6 + 2, x_58);
x_63 = 1;
x_64 = l_Lean_Elab_Term_elabTerm(x_44, x_6, x_63, x_62, x_8, x_9, x_10, x_11, x_12, x_17);
return x_64;
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
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_870____closed__1;
x_2 = l_myMacro____x40_Init_Notation___hyg_11811____closed__1;
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
x_19 = l_Lean_Meta_whnf(x_12, x_6, x_7, x_8, x_9, x_10);
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
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Elab_Term_elabTermEnsuringType(x_24, x_25, x_31, x_26, x_3, x_4, x_32, x_7, x_8, x_9, x_21);
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
x_84 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_83, x_3, x_4, x_6, x_7, x_8, x_9, x_82);
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
lean_dec(x_4);
lean_dec(x_3);
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
x_45 = l_Std_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_18);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_34);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_34);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_22);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_KernelException_toMessageData___closed__15;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_60 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_59, x_58, x_3, x_4, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get_uint8(x_27, 4);
x_93 = lean_ctor_get_uint8(x_27, 5);
x_94 = lean_ctor_get_uint8(x_27, 6);
x_95 = lean_ctor_get_uint8(x_27, 7);
x_96 = lean_ctor_get_uint8(x_27, 8);
lean_dec(x_27);
x_97 = 1;
x_98 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_98, 0, x_97);
lean_ctor_set_uint8(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, 2, x_97);
lean_ctor_set_uint8(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, 4, x_92);
lean_ctor_set_uint8(x_98, 5, x_93);
lean_ctor_set_uint8(x_98, 6, x_94);
lean_ctor_set_uint8(x_98, 7, x_95);
lean_ctor_set_uint8(x_98, 8, x_96);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_28);
lean_ctor_set(x_99, 2, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_100 = l_Lean_Elab_Term_elabTermEnsuringType(x_24, x_25, x_97, x_26, x_3, x_4, x_99, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_137 = lean_st_ref_get(x_9, x_102);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 3);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_ctor_get_uint8(x_139, sizeof(void*)*1);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = 0;
x_104 = x_142;
x_105 = x_141;
goto block_136;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
lean_dec(x_137);
x_144 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_145 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_144, x_3, x_4, x_6, x_7, x_8, x_9, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_unbox(x_146);
lean_dec(x_146);
x_104 = x_148;
x_105 = x_147;
goto block_136;
}
block_136:
{
if (x_104 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_expr_instantiate1(x_23, x_101);
lean_dec(x_23);
x_107 = lean_array_push(x_15, x_101);
if (lean_is_scalar(x_16)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_16;
}
lean_ctor_set(x_108, 0, x_18);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_13)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_13;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_103);
lean_inc(x_18);
x_112 = l_Std_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_18);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__7;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_List_foldl___at_Lean_Meta_Match_Example_toMessageData___spec__1___closed__1;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
lean_inc(x_101);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_101);
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_22);
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_KernelException_toMessageData___closed__15;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_127 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_126, x_125, x_3, x_4, x_6, x_7, x_8, x_9, x_105);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = lean_expr_instantiate1(x_23, x_101);
lean_dec(x_23);
x_131 = lean_array_push(x_15, x_101);
if (lean_is_scalar(x_16)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_16;
}
lean_ctor_set(x_132, 0, x_18);
lean_ctor_set(x_132, 1, x_131);
if (lean_is_scalar(x_13)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_13;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_128);
return x_135;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
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
lean_dec(x_4);
lean_dec(x_3);
x_149 = lean_ctor_get(x_100, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_100, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_151 = x_100;
} else {
 lean_dec_ref(x_100);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_153 = lean_ctor_get(x_19, 1);
lean_inc(x_153);
lean_dec(x_19);
x_154 = lean_array_get_size(x_2);
x_155 = l_Std_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_154);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__2;
x_158 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__4;
x_160 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_160, x_3, x_4, x_6, x_7, x_8, x_9, x_153);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
return x_161;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_161);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_166 = !lean_is_exclusive(x_19);
if (x_166 == 0)
{
return x_19;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_19, 0);
x_168 = lean_ctor_get(x_19, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_19);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___boxed), 10, 5);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_7);
lean_closure_set(x_20, 3, x_8);
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
x_16 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
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
lean_dec(x_2);
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
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_instantiateMVars(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_isFVar(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
x_16 = l_Lean_Expr_toHeadIndex(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_17);
x_19 = lean_st_ref_get(x_9, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_9);
x_25 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_16, x_18, x_13, x_17, x_23, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_9, x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(0);
x_40 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_11);
x_41 = l_Lean_Expr_toHeadIndex(x_2);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_42);
x_44 = lean_st_ref_get(x_9, x_14);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_st_mk_ref(x_46, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_9);
x_50 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_41, x_43, x_13, x_42, x_48, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_43);
lean_dec(x_41);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_9, x_52);
lean_dec(x_9);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_48, x_54);
lean_dec(x_48);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_48);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = l_Lean_mkOptionalNode___closed__2;
x_65 = lean_array_push(x_64, x_2);
x_66 = lean_expr_abstract(x_13, x_65);
lean_dec(x_65);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_66);
return x_11;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
x_69 = l_Lean_Expr_isFVar(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = l_Lean_Expr_toHeadIndex(x_2);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_71);
x_73 = lean_st_ref_get(x_9, x_68);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_st_mk_ref(x_75, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_9);
x_79 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_70, x_72, x_67, x_71, x_77, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_72);
lean_dec(x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_9, x_81);
lean_dec(x_9);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_st_ref_get(x_77, x_83);
lean_dec(x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_77);
lean_dec(x_9);
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_90 = x_79;
} else {
 lean_dec_ref(x_79);
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
lean_object* x_92; uint8_t x_93; 
x_92 = lean_box(0);
x_93 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = l_Lean_Expr_toHeadIndex(x_2);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_95);
x_97 = lean_st_ref_get(x_9, x_68);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_st_mk_ref(x_99, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_9);
x_103 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_94, x_96, x_67, x_95, x_101, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_96);
lean_dec(x_94);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_9, x_105);
lean_dec(x_9);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_101, x_107);
lean_dec(x_101);
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
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_101);
lean_dec(x_9);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_116 = l_Lean_mkOptionalNode___closed__2;
x_117 = lean_array_push(x_116, x_2);
x_118 = lean_expr_abstract(x_67, x_117);
lean_dec(x_117);
lean_dec(x_67);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_68);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_11);
if (x_120 == 0)
{
return x_11;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_11, 0);
x_122 = lean_ctor_get(x_11, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_11);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Meta_mkEq___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_expr_instantiate1(x_1, x_2);
x_18 = l_Lean_Syntax_mkApp___closed__1;
x_19 = lean_array_push(x_18, x_2);
x_20 = lean_array_push(x_19, x_9);
lean_inc(x_12);
x_21 = l_Lean_Meta_mkForallFVars(x_20, x_17, x_12, x_13, x_14, x_15, x_16);
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
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_3, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_push(x_4, x_25);
x_28 = lean_array_push(x_27, x_3);
x_29 = lean_array_get_size(x_5);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = x_5;
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(x_6, x_7, x_30, x_31, x_32);
x_34 = x_33;
x_35 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop(x_8, x_6, x_28, x_22, x_34, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
return x_35;
}
else
{
uint8_t x_36; 
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
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
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
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_1, x_8, x_11, x_12, x_13, x_14, x_15);
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
x_17 = l_Lean_instInhabitedSyntax;
x_18 = lean_array_get(x_17, x_1, x_16);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabAtomicDiscr(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Meta_instantiateMVars(x_20, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_25 = l_Lean_Meta_inferType(x_23, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_Meta_instantiateMVars(x_26, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
return x_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_28, 0);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_28);
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
x_60 = !lean_is_exclusive(x_25);
if (x_60 == 0)
{
return x_25;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_25, 0);
x_62 = lean_ctor_get(x_25, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_25);
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
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
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
x_68 = !lean_is_exclusive(x_19);
if (x_68 == 0)
{
return x_19;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_19, 0);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_19);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_72 = l_Array_reverse___rarg(x_3);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_4);
lean_ctor_set(x_73, 1, x_5);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_12);
return x_75;
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchTypeAndDiscrs_loop___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_1);
return x_8;
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
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
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1;
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed), 5, 3);
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
x_43 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1;
x_44 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed), 5, 3);
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
x_9 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed), 5, 3);
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
x_3 = lean_unsigned_to_nat(127u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
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
x_11 = l_myMacro____x40_Init_Notation___hyg_11811____closed__12;
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
x_27 = l_Lean_Syntax_SepArray_getElems___rarg(x_26);
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
x_3 = lean_unsigned_to_nat(128u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_myMacro____x40_Init_Notation___hyg_11811____closed__2;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_11 = l_Lean_Syntax_isOfKind(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_14 = lean_panic_fn(x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_Syntax_getArgs(x_8);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_1);
x_19 = l_Array_empty___closed__1;
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_21 = lean_panic_fn(x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_8, x_22);
lean_dec(x_8);
x_24 = l_Lean_expandExplicitBindersAux_loop___closed__6;
x_25 = l_Lean_Syntax_isOfKind(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = l_Array_empty___closed__1;
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_28 = lean_panic_fn(x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
lean_dec(x_1);
x_31 = l_myMacro____x40_Init_Notation___hyg_11811____closed__11;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_33 = l_Array_empty___closed__1;
x_34 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_35 = lean_panic_fn(x_33, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = l_Lean_Syntax_getArg(x_30, x_22);
lean_dec(x_30);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_38 = lean_array_get_size(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
x_41 = x_37;
x_42 = l_myMacro____x40_Init_Notation___hyg_2094____closed__2;
x_43 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(x_42, x_39, x_40, x_41);
x_44 = x_43;
return x_44;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_8);
x_45 = lean_unsigned_to_nat(4u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
lean_dec(x_1);
x_47 = l_myMacro____x40_Init_Notation___hyg_11811____closed__11;
lean_inc(x_46);
x_48 = l_Lean_Syntax_isOfKind(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
x_49 = l_Array_empty___closed__1;
x_50 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___closed__1;
x_51 = lean_panic_fn(x_49, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Syntax_getArg(x_46, x_52);
lean_dec(x_46);
x_54 = l_Lean_Syntax_getArgs(x_53);
lean_dec(x_53);
x_55 = lean_array_get_size(x_54);
x_56 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_57 = 0;
x_58 = x_54;
x_59 = l_myMacro____x40_Init_Notation___hyg_2094____closed__2;
x_60 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts___spec__1(x_59, x_56, x_57, x_58);
x_61 = x_60;
return x_61;
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
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MVarWithIdKind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2;
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
x_10 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2;
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
x_18 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2;
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
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2;
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
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__3___rarg___lambda__1), 10, 3);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg___boxed), 9, 0);
return x_2;
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
x_10 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_1);
x_11 = l_Lean_MessageData_ofList(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_KernelException_toMessageData___closed__15;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_List_filterAux___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_map___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__3(lean_object* x_1) {
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
x_6 = l_List_map___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__3(x_5);
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
x_10 = l_List_map___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__3(x_9);
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
x_11 = l_List_filterAux___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_1, x_10);
x_12 = l_List_map___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__3(x_11);
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
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__4() {
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
x_12 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__4;
x_13 = lean_box(0);
lean_inc(x_7);
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
x_20 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3;
x_21 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__46;
x_25 = lean_array_push(x_24, x_23);
x_26 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__43;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_ctor_get(x_1, 6);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_Syntax_mkApp(x_27, x_28);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__46;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__43;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_ctor_get(x_1, 6);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Syntax_mkApp(x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
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
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__6;
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
x_3 = lean_unsigned_to_nat(287u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
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
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_11811____closed__22;
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3;
x_34 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_3, 5);
lean_dec(x_36);
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_dec(x_12);
lean_ctor_set(x_3, 5, x_38);
x_39 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_3, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_44 = lean_ctor_get(x_3, 2);
x_45 = lean_ctor_get(x_3, 3);
x_46 = lean_ctor_get(x_3, 4);
x_47 = lean_ctor_get(x_3, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_48 = lean_ctor_get(x_12, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_dec(x_12);
x_50 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*7, x_42);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 1, x_43);
x_51 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_pushNewArg(x_1, x_2, x_50, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_51;
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
x_28 = l_Array_findIdx_x3f_loop___rarg(x_22, x_25, x_26, x_27, lean_box(0));
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_23 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ConstantInfo_type(x_24);
x_27 = lean_box(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed), 18, 8);
lean_closure_set(x_28, 0, x_24);
lean_closure_set(x_28, 1, x_22);
lean_closure_set(x_28, 2, x_14);
lean_closure_set(x_28, 3, x_15);
lean_closure_set(x_28, 4, x_27);
lean_closure_set(x_28, 5, x_2);
lean_closure_set(x_28, 6, x_3);
lean_closure_set(x_28, 7, x_4);
x_29 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(x_26, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_22);
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
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_35;
}
}
}
else
{
uint8_t x_36; 
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
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
x_17 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__43;
lean_inc(x_2);
x_18 = l_Lean_Syntax_isOfKind(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3;
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
x_28 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3;
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
lean_dec(x_2);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_21 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_20);
x_23 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_10);
lean_dec(x_22);
return x_23;
}
}
}
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_17, x_1, x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_st_ref_set(x_4, x_23, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
x_11 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3;
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_1 = l_Lean_instToExprName___closed__1;
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5() {
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
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprName___closed__1;
x_2 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_861____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_861____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprName___closed__1;
x_2 = l_rawNatLit___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l_rawNatLit___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
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
x_15 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_16 = l_Lean_addMacroScope(x_14, x_15, x_10);
x_17 = l_Lean_instInhabitedSourceInfo___closed__1;
x_18 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_19 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
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
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_24 = l_Lean_addMacroScope(x_21, x_23, x_10);
x_25 = l_Lean_instInhabitedSourceInfo___closed__1;
x_26 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
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
x_41 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_42 = l_Lean_addMacroScope(x_40, x_41, x_36);
x_43 = l_Lean_instInhabitedSourceInfo___closed__1;
x_44 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
x_45 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Array_empty___closed__1;
x_48 = lean_array_push(x_47, x_46);
x_49 = lean_array_push(x_47, x_33);
x_50 = l_Lean_Syntax_mkStrLit(x_31, x_43);
lean_dec(x_31);
x_51 = lean_array_push(x_49, x_50);
x_52 = l_myMacro____x40_Init_Notation___hyg_11811____closed__22;
x_53 = lean_array_push(x_51, x_52);
x_54 = l_Lean_nullKind___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_48, x_55);
x_57 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
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
x_61 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_62 = l_Lean_addMacroScope(x_59, x_61, x_36);
x_63 = l_Lean_instInhabitedSourceInfo___closed__1;
x_64 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
x_65 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_65);
x_67 = l_Array_empty___closed__1;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_array_push(x_67, x_33);
x_70 = l_Lean_Syntax_mkStrLit(x_31, x_63);
lean_dec(x_31);
x_71 = lean_array_push(x_69, x_70);
x_72 = l_myMacro____x40_Init_Notation___hyg_11811____closed__22;
x_73 = lean_array_push(x_71, x_72);
x_74 = l_Lean_nullKind___closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_array_push(x_68, x_75);
x_77 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
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
x_91 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_92 = l_Lean_addMacroScope(x_90, x_91, x_86);
x_93 = l_Lean_instInhabitedSourceInfo___closed__1;
x_94 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_95 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
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
x_102 = l_Lean_Syntax_mkLit(x_101, x_100, x_93);
x_103 = lean_array_push(x_99, x_102);
x_104 = l_myMacro____x40_Init_Notation___hyg_11811____closed__22;
x_105 = lean_array_push(x_103, x_104);
x_106 = l_Lean_nullKind___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_98, x_107);
x_109 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
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
x_113 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_114 = l_Lean_addMacroScope(x_111, x_113, x_86);
x_115 = l_Lean_instInhabitedSourceInfo___closed__1;
x_116 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_117 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
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
x_124 = l_Lean_Syntax_mkLit(x_123, x_122, x_115);
x_125 = lean_array_push(x_121, x_124);
x_126 = l_myMacro____x40_Init_Notation___hyg_11811____closed__22;
x_127 = lean_array_push(x_125, x_126);
x_128 = l_Lean_nullKind___closed__2;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_array_push(x_120, x_129);
x_131 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
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
x_9 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed), 11, 3);
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
x_12 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
x_13 = lean_name_eq(x_10, x_12);
if (x_13 == 0)
{
uint8_t x_1203; 
x_1203 = 0;
x_14 = x_1203;
goto block_1202;
}
else
{
uint8_t x_1204; 
x_1204 = 1;
x_14 = x_1204;
goto block_1202;
}
block_1202:
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
x_33 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_261____closed__2;
x_34 = lean_name_eq(x_10, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
x_36 = lean_name_eq(x_10, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_72);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_75);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_80 = l_Lean_addMacroScope(x_78, x_79, x_74);
x_81 = l_Lean_instInhabitedSourceInfo___closed__1;
x_82 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_83 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_83);
x_85 = l_Array_empty___closed__1;
x_86 = lean_array_push(x_85, x_84);
x_87 = lean_array_push(x_85, x_62);
x_88 = lean_array_push(x_87, x_71);
x_89 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_88);
lean_ctor_set(x_1, 0, x_89);
x_90 = lean_array_push(x_86, x_1);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_12);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_76, 0, x_91);
return x_76;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_76, 0);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_76);
x_94 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_95 = l_Lean_addMacroScope(x_92, x_94, x_74);
x_96 = l_Lean_instInhabitedSourceInfo___closed__1;
x_97 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_98 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_99 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set(x_99, 2, x_95);
lean_ctor_set(x_99, 3, x_98);
x_100 = l_Array_empty___closed__1;
x_101 = lean_array_push(x_100, x_99);
x_102 = lean_array_push(x_100, x_62);
x_103 = lean_array_push(x_102, x_71);
x_104 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_104);
x_105 = lean_array_push(x_101, x_1);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_93);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_free_object(x_1);
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = !lean_is_exclusive(x_70);
if (x_108 == 0)
{
return x_70;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_70, 0);
x_110 = lean_ctor_get(x_70, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_70);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_112 = l_Lean_Elab_Term_CollectPatternVars_collect(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_117);
lean_dec(x_8);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_123 = l_Lean_addMacroScope(x_119, x_122, x_116);
x_124 = l_Lean_instInhabitedSourceInfo___closed__1;
x_125 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_126 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_127 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
lean_ctor_set(x_127, 2, x_123);
lean_ctor_set(x_127, 3, x_126);
x_128 = l_Array_empty___closed__1;
x_129 = lean_array_push(x_128, x_127);
x_130 = lean_array_push(x_128, x_62);
x_131 = lean_array_push(x_130, x_113);
x_132 = l_Lean_nullKind___closed__2;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_array_push(x_129, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_12);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_121)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_121;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_120);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_137 = lean_ctor_get(x_112, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_112, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_139 = x_112;
} else {
 lean_dec_ref(x_112);
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
else
{
uint8_t x_141; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_63);
if (x_141 == 0)
{
return x_63;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_63, 0);
x_143 = lean_ctor_get(x_63, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_63);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_free_object(x_25);
lean_dec(x_10);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Syntax_getArg(x_1, x_145);
lean_dec(x_1);
x_147 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_148 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_147, x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = l_Lean_instInhabitedSyntax;
x_150 = lean_array_get(x_149, x_11, x_23);
x_151 = l_Lean_Syntax_isNone(x_150);
if (x_151 == 0)
{
uint8_t x_152; 
lean_free_object(x_25);
x_152 = !lean_is_exclusive(x_1);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_1, 1);
lean_dec(x_153);
x_154 = lean_ctor_get(x_1, 0);
lean_dec(x_154);
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Lean_Syntax_getArg(x_150, x_155);
x_157 = l_Lean_Syntax_getArg(x_150, x_23);
x_158 = l_Lean_Syntax_isNone(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = l_Lean_Syntax_getArg(x_157, x_155);
lean_inc(x_159);
x_160 = l_Lean_Syntax_getKind(x_159);
x_161 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_162 = lean_name_eq(x_160, x_161);
lean_dec(x_160);
if (x_162 == 0)
{
lean_object* x_163; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_163 = l_Lean_Elab_Term_CollectPatternVars_collect(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Syntax_setArg(x_150, x_155, x_164);
x_167 = l_Lean_Syntax_getArg(x_159, x_23);
x_168 = l_Lean_Syntax_getArgs(x_167);
lean_dec(x_167);
x_169 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_170 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_168, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_165);
lean_dec(x_168);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_172);
lean_ctor_set(x_1, 0, x_173);
x_174 = l_Lean_Syntax_setArg(x_159, x_23, x_1);
x_175 = l_Lean_Syntax_setArg(x_157, x_155, x_174);
x_176 = l_Lean_Syntax_setArg(x_166, x_23, x_175);
x_177 = lean_array_set(x_11, x_23, x_176);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_10);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_170, 0, x_178);
return x_170;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_170, 0);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_170);
x_181 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_179);
lean_ctor_set(x_1, 0, x_181);
x_182 = l_Lean_Syntax_setArg(x_159, x_23, x_1);
x_183 = l_Lean_Syntax_setArg(x_157, x_155, x_182);
x_184 = l_Lean_Syntax_setArg(x_166, x_23, x_183);
x_185 = lean_array_set(x_11, x_23, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_10);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_180);
return x_187;
}
}
else
{
uint8_t x_188; 
lean_dec(x_166);
lean_dec(x_159);
lean_dec(x_157);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_188 = !lean_is_exclusive(x_170);
if (x_188 == 0)
{
return x_170;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_170, 0);
x_190 = lean_ctor_get(x_170, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_170);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_159);
lean_dec(x_157);
lean_free_object(x_1);
lean_dec(x_150);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_163);
if (x_192 == 0)
{
return x_163;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_163, 0);
x_194 = lean_ctor_get(x_163, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_163);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_159);
lean_dec(x_157);
x_196 = l_Lean_Elab_Term_CollectPatternVars_collect(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_196, 0);
x_199 = l_Lean_Syntax_setArg(x_150, x_155, x_198);
x_200 = lean_array_set(x_11, x_23, x_199);
lean_ctor_set(x_1, 1, x_200);
lean_ctor_set(x_196, 0, x_1);
return x_196;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_196, 0);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_196);
x_203 = l_Lean_Syntax_setArg(x_150, x_155, x_201);
x_204 = lean_array_set(x_11, x_23, x_203);
lean_ctor_set(x_1, 1, x_204);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_1);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_free_object(x_1);
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_206 = !lean_is_exclusive(x_196);
if (x_206 == 0)
{
return x_196;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_196, 0);
x_208 = lean_ctor_get(x_196, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_196);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
else
{
lean_object* x_210; 
lean_dec(x_157);
x_210 = l_Lean_Elab_Term_CollectPatternVars_collect(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = l_Lean_Syntax_setArg(x_150, x_155, x_212);
x_214 = lean_array_set(x_11, x_23, x_213);
lean_ctor_set(x_1, 1, x_214);
lean_ctor_set(x_210, 0, x_1);
return x_210;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_210, 0);
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_210);
x_217 = l_Lean_Syntax_setArg(x_150, x_155, x_215);
x_218 = lean_array_set(x_11, x_23, x_217);
lean_ctor_set(x_1, 1, x_218);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_1);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
}
else
{
uint8_t x_220; 
lean_free_object(x_1);
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_220 = !lean_is_exclusive(x_210);
if (x_220 == 0)
{
return x_210;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_210, 0);
x_222 = lean_ctor_get(x_210, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_210);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_1);
x_224 = lean_unsigned_to_nat(0u);
x_225 = l_Lean_Syntax_getArg(x_150, x_224);
x_226 = l_Lean_Syntax_getArg(x_150, x_23);
x_227 = l_Lean_Syntax_isNone(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = l_Lean_Syntax_getArg(x_226, x_224);
lean_inc(x_228);
x_229 = l_Lean_Syntax_getKind(x_228);
x_230 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_231 = lean_name_eq(x_229, x_230);
lean_dec(x_229);
if (x_231 == 0)
{
lean_object* x_232; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_232 = l_Lean_Elab_Term_CollectPatternVars_collect(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Syntax_setArg(x_150, x_224, x_233);
x_236 = l_Lean_Syntax_getArg(x_228, x_23);
x_237 = l_Lean_Syntax_getArgs(x_236);
lean_dec(x_236);
x_238 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_239 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_237, x_238, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_234);
lean_dec(x_237);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_242 = x_239;
} else {
 lean_dec_ref(x_239);
 x_242 = lean_box(0);
}
x_243 = l_Lean_nullKind;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_240);
x_245 = l_Lean_Syntax_setArg(x_228, x_23, x_244);
x_246 = l_Lean_Syntax_setArg(x_226, x_224, x_245);
x_247 = l_Lean_Syntax_setArg(x_235, x_23, x_246);
x_248 = lean_array_set(x_11, x_23, x_247);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_10);
lean_ctor_set(x_249, 1, x_248);
if (lean_is_scalar(x_242)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_242;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_241);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_235);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_11);
lean_dec(x_10);
x_251 = lean_ctor_get(x_239, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_239, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_253 = x_239;
} else {
 lean_dec_ref(x_239);
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
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_150);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_255 = lean_ctor_get(x_232, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_232, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_257 = x_232;
} else {
 lean_dec_ref(x_232);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; 
lean_dec(x_228);
lean_dec(x_226);
x_259 = l_Lean_Elab_Term_CollectPatternVars_collect(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
x_263 = l_Lean_Syntax_setArg(x_150, x_224, x_260);
x_264 = lean_array_set(x_11, x_23, x_263);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_10);
lean_ctor_set(x_265, 1, x_264);
if (lean_is_scalar(x_262)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_262;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_261);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_267 = lean_ctor_get(x_259, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_259, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_269 = x_259;
} else {
 lean_dec_ref(x_259);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
else
{
lean_object* x_271; 
lean_dec(x_226);
x_271 = l_Lean_Elab_Term_CollectPatternVars_collect(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_275 = l_Lean_Syntax_setArg(x_150, x_224, x_272);
x_276 = lean_array_set(x_11, x_23, x_275);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_10);
lean_ctor_set(x_277, 1, x_276);
if (lean_is_scalar(x_274)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_274;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_273);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_279 = lean_ctor_get(x_271, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_271, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_281 = x_271;
} else {
 lean_dec_ref(x_271);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
}
else
{
lean_dec(x_150);
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
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
lean_dec(x_3);
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_283 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_27);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_st_ref_get(x_8, x_285);
lean_dec(x_8);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_st_ref_take(x_2, x_287);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = !lean_is_exclusive(x_289);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_292 = lean_ctor_get(x_289, 1);
x_293 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_284);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_295 = lean_array_push(x_292, x_294);
lean_ctor_set(x_289, 1, x_295);
x_296 = lean_st_ref_set(x_2, x_289, x_290);
lean_dec(x_2);
x_297 = !lean_is_exclusive(x_296);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_296, 0);
lean_dec(x_298);
lean_ctor_set(x_296, 0, x_284);
return x_296;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
lean_dec(x_296);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_284);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_301 = lean_ctor_get(x_289, 0);
x_302 = lean_ctor_get(x_289, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_289);
x_303 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_284);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = lean_array_push(x_302, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_301);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_st_ref_set(x_2, x_306, x_290);
lean_dec(x_2);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_284);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
lean_free_object(x_25);
lean_dec(x_1);
x_311 = l_Lean_instInhabitedSyntax;
x_312 = lean_array_get(x_311, x_11, x_23);
x_313 = l_Lean_Syntax_isNone(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
lean_dec(x_11);
lean_dec(x_10);
x_314 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_315 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_312, x_314, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_312);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
return x_315;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_315, 0);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_315);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_312);
x_320 = lean_box(0);
x_321 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_320, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_321;
}
}
}
else
{
uint8_t x_322; 
lean_free_object(x_25);
x_322 = !lean_is_exclusive(x_1);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_323 = lean_ctor_get(x_1, 1);
lean_dec(x_323);
x_324 = lean_ctor_get(x_1, 0);
lean_dec(x_324);
x_325 = l_Lean_instInhabitedSyntax;
x_326 = lean_array_get(x_325, x_11, x_23);
x_327 = l_Lean_Syntax_getArgs(x_326);
lean_dec(x_326);
x_328 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_329 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_327, x_328, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_327);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_ctor_get(x_329, 0);
x_332 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_331);
lean_ctor_set(x_1, 0, x_332);
x_333 = lean_array_set(x_11, x_23, x_1);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_10);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set(x_329, 0, x_334);
return x_329;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_335 = lean_ctor_get(x_329, 0);
x_336 = lean_ctor_get(x_329, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_329);
x_337 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_335);
lean_ctor_set(x_1, 0, x_337);
x_338 = lean_array_set(x_11, x_23, x_1);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_10);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_336);
return x_340;
}
}
else
{
uint8_t x_341; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_341 = !lean_is_exclusive(x_329);
if (x_341 == 0)
{
return x_329;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_329, 0);
x_343 = lean_ctor_get(x_329, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_329);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_1);
x_345 = l_Lean_instInhabitedSyntax;
x_346 = lean_array_get(x_345, x_11, x_23);
x_347 = l_Lean_Syntax_getArgs(x_346);
lean_dec(x_346);
x_348 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_349 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_347, x_348, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_347);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_352 = x_349;
} else {
 lean_dec_ref(x_349);
 x_352 = lean_box(0);
}
x_353 = l_Lean_nullKind;
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_350);
x_355 = lean_array_set(x_11, x_23, x_354);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_10);
lean_ctor_set(x_356, 1, x_355);
if (lean_is_scalar(x_352)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_352;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_351);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_11);
lean_dec(x_10);
x_358 = lean_ctor_get(x_349, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_349, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_360 = x_349;
} else {
 lean_dec_ref(x_349);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_362 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_363 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_362, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_1);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; 
x_364 = lean_ctor_get(x_3, 0);
x_365 = lean_ctor_get(x_3, 1);
x_366 = lean_ctor_get(x_3, 2);
x_367 = lean_ctor_get(x_3, 3);
x_368 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_369 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_370 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_371 = lean_ctor_get(x_3, 5);
lean_inc(x_371);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_3);
x_372 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_372, 0, x_364);
lean_ctor_set(x_372, 1, x_365);
lean_ctor_set(x_372, 2, x_366);
lean_ctor_set(x_372, 3, x_367);
lean_ctor_set(x_372, 4, x_22);
lean_ctor_set(x_372, 5, x_371);
lean_ctor_set_uint8(x_372, sizeof(void*)*6, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*6 + 1, x_369);
lean_ctor_set_uint8(x_372, sizeof(void*)*6 + 2, x_370);
if (x_14 == 0)
{
lean_object* x_373; uint8_t x_374; 
x_373 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_374 = lean_name_eq(x_10, x_373);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_261____closed__2;
x_376 = lean_name_eq(x_10, x_375);
if (x_376 == 0)
{
lean_object* x_377; uint8_t x_378; 
x_377 = l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
x_378 = lean_name_eq(x_10, x_377);
if (x_378 == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
x_380 = lean_name_eq(x_10, x_379);
if (x_380 == 0)
{
lean_object* x_381; uint8_t x_382; 
lean_dec(x_11);
x_381 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_382 = lean_name_eq(x_10, x_381);
if (x_382 == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_384 = lean_name_eq(x_10, x_383);
if (x_384 == 0)
{
lean_object* x_385; uint8_t x_386; 
x_385 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_386 = lean_name_eq(x_10, x_385);
if (x_386 == 0)
{
lean_object* x_387; uint8_t x_388; 
x_387 = l_Lean_strLitKind;
x_388 = lean_name_eq(x_10, x_387);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = l_Lean_numLitKind;
x_390 = lean_name_eq(x_10, x_389);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = l_Lean_scientificLitKind;
x_392 = lean_name_eq(x_10, x_391);
if (x_392 == 0)
{
lean_object* x_393; uint8_t x_394; 
x_393 = l_Lean_charLitKind;
x_394 = lean_name_eq(x_10, x_393);
if (x_394 == 0)
{
lean_object* x_395; uint8_t x_396; 
lean_free_object(x_25);
x_395 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_396 = lean_name_eq(x_10, x_395);
if (x_396 == 0)
{
lean_object* x_397; uint8_t x_398; 
lean_dec(x_1);
x_397 = l_Lean_choiceKind;
x_398 = lean_name_eq(x_10, x_397);
lean_dec(x_10);
if (x_398 == 0)
{
lean_object* x_399; 
x_399 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_372);
lean_dec(x_2);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; 
x_400 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_401 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_400, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_372);
lean_dec(x_2);
return x_401;
}
}
else
{
lean_object* x_402; 
lean_dec(x_10);
lean_dec(x_2);
x_402 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_402;
}
}
else
{
lean_dec(x_372);
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
lean_dec(x_372);
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
lean_dec(x_372);
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
lean_dec(x_372);
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
lean_dec(x_372);
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
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_free_object(x_25);
lean_dec(x_10);
x_403 = lean_unsigned_to_nat(0u);
x_404 = l_Lean_Syntax_getArg(x_1, x_403);
lean_inc(x_7);
lean_inc(x_404);
x_405 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_404, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_ctor_get(x_405, 1);
lean_inc(x_406);
lean_dec(x_405);
x_407 = lean_unsigned_to_nat(2u);
x_408 = l_Lean_Syntax_getArg(x_1, x_407);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_409 = x_1;
} else {
 lean_dec_ref(x_1);
 x_409 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_372);
x_410 = l_Lean_Elab_Term_CollectPatternVars_collect(x_408, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_406);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l_Lean_Elab_Term_getCurrMacroScope(x_372, x_4, x_5, x_6, x_7, x_8, x_412);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_372);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_415);
lean_dec(x_8);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_421 = l_Lean_addMacroScope(x_417, x_420, x_414);
x_422 = l_Lean_instInhabitedSourceInfo___closed__1;
x_423 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_424 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_425 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
lean_ctor_set(x_425, 2, x_421);
lean_ctor_set(x_425, 3, x_424);
x_426 = l_Array_empty___closed__1;
x_427 = lean_array_push(x_426, x_425);
x_428 = lean_array_push(x_426, x_404);
x_429 = lean_array_push(x_428, x_411);
x_430 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_409)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_409;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
x_432 = lean_array_push(x_427, x_431);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_12);
lean_ctor_set(x_433, 1, x_432);
if (lean_is_scalar(x_419)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_419;
}
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_418);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_409);
lean_dec(x_404);
lean_dec(x_372);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_435 = lean_ctor_get(x_410, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_410, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_437 = x_410;
} else {
 lean_dec_ref(x_410);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_404);
lean_dec(x_372);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_439 = lean_ctor_get(x_405, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_405, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_441 = x_405;
} else {
 lean_dec_ref(x_405);
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
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_free_object(x_25);
lean_dec(x_10);
x_443 = lean_unsigned_to_nat(0u);
x_444 = l_Lean_Syntax_getArg(x_1, x_443);
lean_dec(x_1);
x_445 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_446 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_445, x_444, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_447 = l_Lean_instInhabitedSyntax;
x_448 = lean_array_get(x_447, x_11, x_23);
x_449 = l_Lean_Syntax_isNone(x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_450 = x_1;
} else {
 lean_dec_ref(x_1);
 x_450 = lean_box(0);
}
x_451 = lean_unsigned_to_nat(0u);
x_452 = l_Lean_Syntax_getArg(x_448, x_451);
x_453 = l_Lean_Syntax_getArg(x_448, x_23);
x_454 = l_Lean_Syntax_isNone(x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_455 = l_Lean_Syntax_getArg(x_453, x_451);
lean_inc(x_455);
x_456 = l_Lean_Syntax_getKind(x_455);
x_457 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_458 = lean_name_eq(x_456, x_457);
lean_dec(x_456);
if (x_458 == 0)
{
lean_object* x_459; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_372);
lean_inc(x_2);
x_459 = l_Lean_Elab_Term_CollectPatternVars_collect(x_452, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = l_Lean_Syntax_setArg(x_448, x_451, x_460);
x_463 = l_Lean_Syntax_getArg(x_455, x_23);
x_464 = l_Lean_Syntax_getArgs(x_463);
lean_dec(x_463);
x_465 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_466 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_464, x_465, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_461);
lean_dec(x_464);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_469 = x_466;
} else {
 lean_dec_ref(x_466);
 x_469 = lean_box(0);
}
x_470 = l_Lean_nullKind;
if (lean_is_scalar(x_450)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_450;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_467);
x_472 = l_Lean_Syntax_setArg(x_455, x_23, x_471);
x_473 = l_Lean_Syntax_setArg(x_453, x_451, x_472);
x_474 = l_Lean_Syntax_setArg(x_462, x_23, x_473);
x_475 = lean_array_set(x_11, x_23, x_474);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_10);
lean_ctor_set(x_476, 1, x_475);
if (lean_is_scalar(x_469)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_469;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_468);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_462);
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_450);
lean_dec(x_11);
lean_dec(x_10);
x_478 = lean_ctor_get(x_466, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_466, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_480 = x_466;
} else {
 lean_dec_ref(x_466);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_450);
lean_dec(x_448);
lean_dec(x_372);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_482 = lean_ctor_get(x_459, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_484 = x_459;
} else {
 lean_dec_ref(x_459);
 x_484 = lean_box(0);
}
if (lean_is_scalar(x_484)) {
 x_485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_485 = x_484;
}
lean_ctor_set(x_485, 0, x_482);
lean_ctor_set(x_485, 1, x_483);
return x_485;
}
}
else
{
lean_object* x_486; 
lean_dec(x_455);
lean_dec(x_453);
x_486 = l_Lean_Elab_Term_CollectPatternVars_collect(x_452, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_489 = x_486;
} else {
 lean_dec_ref(x_486);
 x_489 = lean_box(0);
}
x_490 = l_Lean_Syntax_setArg(x_448, x_451, x_487);
x_491 = lean_array_set(x_11, x_23, x_490);
if (lean_is_scalar(x_450)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_450;
}
lean_ctor_set(x_492, 0, x_10);
lean_ctor_set(x_492, 1, x_491);
if (lean_is_scalar(x_489)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_489;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_488);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_450);
lean_dec(x_448);
lean_dec(x_11);
lean_dec(x_10);
x_494 = lean_ctor_get(x_486, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_486, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_496 = x_486;
} else {
 lean_dec_ref(x_486);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
return x_497;
}
}
}
else
{
lean_object* x_498; 
lean_dec(x_453);
x_498 = l_Lean_Elab_Term_CollectPatternVars_collect(x_452, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_501 = x_498;
} else {
 lean_dec_ref(x_498);
 x_501 = lean_box(0);
}
x_502 = l_Lean_Syntax_setArg(x_448, x_451, x_499);
x_503 = lean_array_set(x_11, x_23, x_502);
if (lean_is_scalar(x_450)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_450;
}
lean_ctor_set(x_504, 0, x_10);
lean_ctor_set(x_504, 1, x_503);
if (lean_is_scalar(x_501)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_501;
}
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_500);
return x_505;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_450);
lean_dec(x_448);
lean_dec(x_11);
lean_dec(x_10);
x_506 = lean_ctor_get(x_498, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_498, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_508 = x_498;
} else {
 lean_dec_ref(x_498);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
}
else
{
lean_dec(x_448);
lean_dec(x_372);
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
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_372);
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_510 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_27);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_st_ref_get(x_8, x_512);
lean_dec(x_8);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec(x_513);
x_515 = lean_st_ref_take(x_2, x_514);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_520 = x_516;
} else {
 lean_dec_ref(x_516);
 x_520 = lean_box(0);
}
x_521 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_511);
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_521);
x_523 = lean_array_push(x_519, x_522);
if (lean_is_scalar(x_520)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_520;
}
lean_ctor_set(x_524, 0, x_518);
lean_ctor_set(x_524, 1, x_523);
x_525 = lean_st_ref_set(x_2, x_524, x_517);
lean_dec(x_2);
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
lean_ctor_set(x_528, 0, x_511);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; 
lean_free_object(x_25);
lean_dec(x_1);
x_529 = l_Lean_instInhabitedSyntax;
x_530 = lean_array_get(x_529, x_11, x_23);
x_531 = l_Lean_Syntax_isNone(x_530);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_11);
lean_dec(x_10);
x_532 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_533 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_530, x_532, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_372);
lean_dec(x_2);
lean_dec(x_530);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_536 = x_533;
} else {
 lean_dec_ref(x_533);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
else
{
lean_object* x_538; lean_object* x_539; 
lean_dec(x_530);
x_538 = lean_box(0);
x_539 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_538, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
return x_539;
}
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_free_object(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_540 = x_1;
} else {
 lean_dec_ref(x_1);
 x_540 = lean_box(0);
}
x_541 = l_Lean_instInhabitedSyntax;
x_542 = lean_array_get(x_541, x_11, x_23);
x_543 = l_Lean_Syntax_getArgs(x_542);
lean_dec(x_542);
x_544 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_545 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_543, x_544, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_543);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_548 = x_545;
} else {
 lean_dec_ref(x_545);
 x_548 = lean_box(0);
}
x_549 = l_Lean_nullKind;
if (lean_is_scalar(x_540)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_540;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_546);
x_551 = lean_array_set(x_11, x_23, x_550);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_10);
lean_ctor_set(x_552, 1, x_551);
if (lean_is_scalar(x_548)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_548;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_547);
return x_553;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_540);
lean_dec(x_11);
lean_dec(x_10);
x_554 = lean_ctor_get(x_545, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_545, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_556 = x_545;
} else {
 lean_dec_ref(x_545);
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
}
else
{
lean_object* x_558; lean_object* x_559; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
x_558 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_559 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_558, x_1, x_2, x_372, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_1);
return x_559;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; uint8_t x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_560 = lean_ctor_get(x_25, 1);
lean_inc(x_560);
lean_dec(x_25);
x_561 = lean_ctor_get(x_3, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_3, 1);
lean_inc(x_562);
x_563 = lean_ctor_get(x_3, 2);
lean_inc(x_563);
x_564 = lean_ctor_get(x_3, 3);
lean_inc(x_564);
x_565 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_566 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_567 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_568 = lean_ctor_get(x_3, 5);
lean_inc(x_568);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_569 = x_3;
} else {
 lean_dec_ref(x_3);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(0, 6, 3);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_561);
lean_ctor_set(x_570, 1, x_562);
lean_ctor_set(x_570, 2, x_563);
lean_ctor_set(x_570, 3, x_564);
lean_ctor_set(x_570, 4, x_22);
lean_ctor_set(x_570, 5, x_568);
lean_ctor_set_uint8(x_570, sizeof(void*)*6, x_565);
lean_ctor_set_uint8(x_570, sizeof(void*)*6 + 1, x_566);
lean_ctor_set_uint8(x_570, sizeof(void*)*6 + 2, x_567);
if (x_14 == 0)
{
lean_object* x_571; uint8_t x_572; 
x_571 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_572 = lean_name_eq(x_10, x_571);
if (x_572 == 0)
{
lean_object* x_573; uint8_t x_574; 
x_573 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_261____closed__2;
x_574 = lean_name_eq(x_10, x_573);
if (x_574 == 0)
{
lean_object* x_575; uint8_t x_576; 
x_575 = l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
x_576 = lean_name_eq(x_10, x_575);
if (x_576 == 0)
{
lean_object* x_577; uint8_t x_578; 
x_577 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
x_578 = lean_name_eq(x_10, x_577);
if (x_578 == 0)
{
lean_object* x_579; uint8_t x_580; 
lean_dec(x_11);
x_579 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_580 = lean_name_eq(x_10, x_579);
if (x_580 == 0)
{
lean_object* x_581; uint8_t x_582; 
x_581 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_582 = lean_name_eq(x_10, x_581);
if (x_582 == 0)
{
lean_object* x_583; uint8_t x_584; 
x_583 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_584 = lean_name_eq(x_10, x_583);
if (x_584 == 0)
{
lean_object* x_585; uint8_t x_586; 
x_585 = l_Lean_strLitKind;
x_586 = lean_name_eq(x_10, x_585);
if (x_586 == 0)
{
lean_object* x_587; uint8_t x_588; 
x_587 = l_Lean_numLitKind;
x_588 = lean_name_eq(x_10, x_587);
if (x_588 == 0)
{
lean_object* x_589; uint8_t x_590; 
x_589 = l_Lean_scientificLitKind;
x_590 = lean_name_eq(x_10, x_589);
if (x_590 == 0)
{
lean_object* x_591; uint8_t x_592; 
x_591 = l_Lean_charLitKind;
x_592 = lean_name_eq(x_10, x_591);
if (x_592 == 0)
{
lean_object* x_593; uint8_t x_594; 
x_593 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_594 = lean_name_eq(x_10, x_593);
if (x_594 == 0)
{
lean_object* x_595; uint8_t x_596; 
lean_dec(x_1);
x_595 = l_Lean_choiceKind;
x_596 = lean_name_eq(x_10, x_595);
lean_dec(x_10);
if (x_596 == 0)
{
lean_object* x_597; 
x_597 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_570);
lean_dec(x_2);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; 
x_598 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_599 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_598, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_570);
lean_dec(x_2);
return x_599;
}
}
else
{
lean_object* x_600; 
lean_dec(x_10);
lean_dec(x_2);
x_600 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_600;
}
}
else
{
lean_object* x_601; 
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_1);
lean_ctor_set(x_601, 1, x_560);
return x_601;
}
}
else
{
lean_object* x_602; 
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_1);
lean_ctor_set(x_602, 1, x_560);
return x_602;
}
}
else
{
lean_object* x_603; 
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_1);
lean_ctor_set(x_603, 1, x_560);
return x_603;
}
}
else
{
lean_object* x_604; 
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_1);
lean_ctor_set(x_604, 1, x_560);
return x_604;
}
}
else
{
lean_object* x_605; 
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_1);
lean_ctor_set(x_605, 1, x_560);
return x_605;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_10);
x_606 = lean_unsigned_to_nat(0u);
x_607 = l_Lean_Syntax_getArg(x_1, x_606);
lean_inc(x_7);
lean_inc(x_607);
x_608 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_607, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
lean_dec(x_608);
x_610 = lean_unsigned_to_nat(2u);
x_611 = l_Lean_Syntax_getArg(x_1, x_610);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_612 = x_1;
} else {
 lean_dec_ref(x_1);
 x_612 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_570);
x_613 = l_Lean_Elab_Term_CollectPatternVars_collect(x_611, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_609);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = l_Lean_Elab_Term_getCurrMacroScope(x_570, x_4, x_5, x_6, x_7, x_8, x_615);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_570);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_618);
lean_dec(x_8);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_622 = x_619;
} else {
 lean_dec_ref(x_619);
 x_622 = lean_box(0);
}
x_623 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_624 = l_Lean_addMacroScope(x_620, x_623, x_617);
x_625 = l_Lean_instInhabitedSourceInfo___closed__1;
x_626 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_627 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_628 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
lean_ctor_set(x_628, 2, x_624);
lean_ctor_set(x_628, 3, x_627);
x_629 = l_Array_empty___closed__1;
x_630 = lean_array_push(x_629, x_628);
x_631 = lean_array_push(x_629, x_607);
x_632 = lean_array_push(x_631, x_614);
x_633 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_612)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_612;
}
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_632);
x_635 = lean_array_push(x_630, x_634);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_12);
lean_ctor_set(x_636, 1, x_635);
if (lean_is_scalar(x_622)) {
 x_637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_637 = x_622;
}
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_621);
return x_637;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_612);
lean_dec(x_607);
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_638 = lean_ctor_get(x_613, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_613, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_640 = x_613;
} else {
 lean_dec_ref(x_613);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_639);
return x_641;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_607);
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_642 = lean_ctor_get(x_608, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_608, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_644 = x_608;
} else {
 lean_dec_ref(x_608);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_10);
x_646 = lean_unsigned_to_nat(0u);
x_647 = l_Lean_Syntax_getArg(x_1, x_646);
lean_dec(x_1);
x_648 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_649 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_648, x_647, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; uint8_t x_652; 
x_650 = l_Lean_instInhabitedSyntax;
x_651 = lean_array_get(x_650, x_11, x_23);
x_652 = l_Lean_Syntax_isNone(x_651);
if (x_652 == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_653 = x_1;
} else {
 lean_dec_ref(x_1);
 x_653 = lean_box(0);
}
x_654 = lean_unsigned_to_nat(0u);
x_655 = l_Lean_Syntax_getArg(x_651, x_654);
x_656 = l_Lean_Syntax_getArg(x_651, x_23);
x_657 = l_Lean_Syntax_isNone(x_656);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
x_658 = l_Lean_Syntax_getArg(x_656, x_654);
lean_inc(x_658);
x_659 = l_Lean_Syntax_getKind(x_658);
x_660 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_661 = lean_name_eq(x_659, x_660);
lean_dec(x_659);
if (x_661 == 0)
{
lean_object* x_662; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_570);
lean_inc(x_2);
x_662 = l_Lean_Elab_Term_CollectPatternVars_collect(x_655, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = l_Lean_Syntax_setArg(x_651, x_654, x_663);
x_666 = l_Lean_Syntax_getArg(x_658, x_23);
x_667 = l_Lean_Syntax_getArgs(x_666);
lean_dec(x_666);
x_668 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_669 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_667, x_668, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_664);
lean_dec(x_667);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_672 = x_669;
} else {
 lean_dec_ref(x_669);
 x_672 = lean_box(0);
}
x_673 = l_Lean_nullKind;
if (lean_is_scalar(x_653)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_653;
}
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_670);
x_675 = l_Lean_Syntax_setArg(x_658, x_23, x_674);
x_676 = l_Lean_Syntax_setArg(x_656, x_654, x_675);
x_677 = l_Lean_Syntax_setArg(x_665, x_23, x_676);
x_678 = lean_array_set(x_11, x_23, x_677);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_10);
lean_ctor_set(x_679, 1, x_678);
if (lean_is_scalar(x_672)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_672;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_671);
return x_680;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_665);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_653);
lean_dec(x_11);
lean_dec(x_10);
x_681 = lean_ctor_get(x_669, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_669, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_683 = x_669;
} else {
 lean_dec_ref(x_669);
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
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_685 = lean_ctor_get(x_662, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_662, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 x_687 = x_662;
} else {
 lean_dec_ref(x_662);
 x_687 = lean_box(0);
}
if (lean_is_scalar(x_687)) {
 x_688 = lean_alloc_ctor(1, 2, 0);
} else {
 x_688 = x_687;
}
lean_ctor_set(x_688, 0, x_685);
lean_ctor_set(x_688, 1, x_686);
return x_688;
}
}
else
{
lean_object* x_689; 
lean_dec(x_658);
lean_dec(x_656);
x_689 = l_Lean_Elab_Term_CollectPatternVars_collect(x_655, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_689)) {
 lean_ctor_release(x_689, 0);
 lean_ctor_release(x_689, 1);
 x_692 = x_689;
} else {
 lean_dec_ref(x_689);
 x_692 = lean_box(0);
}
x_693 = l_Lean_Syntax_setArg(x_651, x_654, x_690);
x_694 = lean_array_set(x_11, x_23, x_693);
if (lean_is_scalar(x_653)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_653;
}
lean_ctor_set(x_695, 0, x_10);
lean_ctor_set(x_695, 1, x_694);
if (lean_is_scalar(x_692)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_692;
}
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_691);
return x_696;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_11);
lean_dec(x_10);
x_697 = lean_ctor_get(x_689, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_689, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_689)) {
 lean_ctor_release(x_689, 0);
 lean_ctor_release(x_689, 1);
 x_699 = x_689;
} else {
 lean_dec_ref(x_689);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
}
else
{
lean_object* x_701; 
lean_dec(x_656);
x_701 = l_Lean_Elab_Term_CollectPatternVars_collect(x_655, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_704 = x_701;
} else {
 lean_dec_ref(x_701);
 x_704 = lean_box(0);
}
x_705 = l_Lean_Syntax_setArg(x_651, x_654, x_702);
x_706 = lean_array_set(x_11, x_23, x_705);
if (lean_is_scalar(x_653)) {
 x_707 = lean_alloc_ctor(1, 2, 0);
} else {
 x_707 = x_653;
}
lean_ctor_set(x_707, 0, x_10);
lean_ctor_set(x_707, 1, x_706);
if (lean_is_scalar(x_704)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_704;
}
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_703);
return x_708;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_653);
lean_dec(x_651);
lean_dec(x_11);
lean_dec(x_10);
x_709 = lean_ctor_get(x_701, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_701, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_711 = x_701;
} else {
 lean_dec_ref(x_701);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
}
else
{
lean_object* x_713; 
lean_dec(x_651);
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_1);
lean_ctor_set(x_713, 1, x_560);
return x_713;
}
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_570);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_714 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_560);
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
x_717 = lean_st_ref_get(x_8, x_716);
lean_dec(x_8);
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
lean_dec(x_717);
x_719 = lean_st_ref_take(x_2, x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = lean_ctor_get(x_720, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_720, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_724 = x_720;
} else {
 lean_dec_ref(x_720);
 x_724 = lean_box(0);
}
x_725 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_715);
x_726 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_726, 0, x_725);
x_727 = lean_array_push(x_723, x_726);
if (lean_is_scalar(x_724)) {
 x_728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_728 = x_724;
}
lean_ctor_set(x_728, 0, x_722);
lean_ctor_set(x_728, 1, x_727);
x_729 = lean_st_ref_set(x_2, x_728, x_721);
lean_dec(x_2);
x_730 = lean_ctor_get(x_729, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_731 = x_729;
} else {
 lean_dec_ref(x_729);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_715);
lean_ctor_set(x_732, 1, x_730);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; uint8_t x_735; 
lean_dec(x_1);
x_733 = l_Lean_instInhabitedSyntax;
x_734 = lean_array_get(x_733, x_11, x_23);
x_735 = l_Lean_Syntax_isNone(x_734);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_11);
lean_dec(x_10);
x_736 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_737 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_734, x_736, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_570);
lean_dec(x_2);
lean_dec(x_734);
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_737, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_740 = x_737;
} else {
 lean_dec_ref(x_737);
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
else
{
lean_object* x_742; lean_object* x_743; 
lean_dec(x_734);
x_742 = lean_box(0);
x_743 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_742, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
return x_743;
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_744 = x_1;
} else {
 lean_dec_ref(x_1);
 x_744 = lean_box(0);
}
x_745 = l_Lean_instInhabitedSyntax;
x_746 = lean_array_get(x_745, x_11, x_23);
x_747 = l_Lean_Syntax_getArgs(x_746);
lean_dec(x_746);
x_748 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_749 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_747, x_748, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
lean_dec(x_747);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 lean_ctor_release(x_749, 1);
 x_752 = x_749;
} else {
 lean_dec_ref(x_749);
 x_752 = lean_box(0);
}
x_753 = l_Lean_nullKind;
if (lean_is_scalar(x_744)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_744;
}
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_750);
x_755 = lean_array_set(x_11, x_23, x_754);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_10);
lean_ctor_set(x_756, 1, x_755);
if (lean_is_scalar(x_752)) {
 x_757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_757 = x_752;
}
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_751);
return x_757;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_744);
lean_dec(x_11);
lean_dec(x_10);
x_758 = lean_ctor_get(x_749, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_749, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 lean_ctor_release(x_749, 1);
 x_760 = x_749;
} else {
 lean_dec_ref(x_749);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_758);
lean_ctor_set(x_761, 1, x_759);
return x_761;
}
}
}
else
{
lean_object* x_762; lean_object* x_763; 
lean_dec(x_11);
lean_dec(x_10);
x_762 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_763 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_762, x_1, x_2, x_570, x_4, x_5, x_6, x_7, x_8, x_560);
lean_dec(x_1);
return x_763;
}
}
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; uint8_t x_778; uint8_t x_779; uint8_t x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_764 = lean_ctor_get(x_19, 0);
x_765 = lean_ctor_get(x_19, 1);
x_766 = lean_ctor_get(x_19, 2);
x_767 = lean_ctor_get(x_19, 3);
lean_inc(x_767);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_19);
x_768 = lean_unsigned_to_nat(1u);
x_769 = lean_nat_add(x_765, x_768);
x_770 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_770, 0, x_764);
lean_ctor_set(x_770, 1, x_769);
lean_ctor_set(x_770, 2, x_766);
lean_ctor_set(x_770, 3, x_767);
x_771 = lean_st_ref_set(x_8, x_770, x_20);
x_772 = lean_ctor_get(x_771, 1);
lean_inc(x_772);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_773 = x_771;
} else {
 lean_dec_ref(x_771);
 x_773 = lean_box(0);
}
x_774 = lean_ctor_get(x_3, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_3, 1);
lean_inc(x_775);
x_776 = lean_ctor_get(x_3, 2);
lean_inc(x_776);
x_777 = lean_ctor_get(x_3, 3);
lean_inc(x_777);
x_778 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_779 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_780 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_781 = lean_ctor_get(x_3, 5);
lean_inc(x_781);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_782 = x_3;
} else {
 lean_dec_ref(x_3);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(0, 6, 3);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_774);
lean_ctor_set(x_783, 1, x_775);
lean_ctor_set(x_783, 2, x_776);
lean_ctor_set(x_783, 3, x_777);
lean_ctor_set(x_783, 4, x_765);
lean_ctor_set(x_783, 5, x_781);
lean_ctor_set_uint8(x_783, sizeof(void*)*6, x_778);
lean_ctor_set_uint8(x_783, sizeof(void*)*6 + 1, x_779);
lean_ctor_set_uint8(x_783, sizeof(void*)*6 + 2, x_780);
if (x_14 == 0)
{
lean_object* x_784; uint8_t x_785; 
x_784 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_785 = lean_name_eq(x_10, x_784);
if (x_785 == 0)
{
lean_object* x_786; uint8_t x_787; 
x_786 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_261____closed__2;
x_787 = lean_name_eq(x_10, x_786);
if (x_787 == 0)
{
lean_object* x_788; uint8_t x_789; 
x_788 = l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
x_789 = lean_name_eq(x_10, x_788);
if (x_789 == 0)
{
lean_object* x_790; uint8_t x_791; 
x_790 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
x_791 = lean_name_eq(x_10, x_790);
if (x_791 == 0)
{
lean_object* x_792; uint8_t x_793; 
lean_dec(x_11);
x_792 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_793 = lean_name_eq(x_10, x_792);
if (x_793 == 0)
{
lean_object* x_794; uint8_t x_795; 
x_794 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_795 = lean_name_eq(x_10, x_794);
if (x_795 == 0)
{
lean_object* x_796; uint8_t x_797; 
x_796 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_797 = lean_name_eq(x_10, x_796);
if (x_797 == 0)
{
lean_object* x_798; uint8_t x_799; 
x_798 = l_Lean_strLitKind;
x_799 = lean_name_eq(x_10, x_798);
if (x_799 == 0)
{
lean_object* x_800; uint8_t x_801; 
x_800 = l_Lean_numLitKind;
x_801 = lean_name_eq(x_10, x_800);
if (x_801 == 0)
{
lean_object* x_802; uint8_t x_803; 
x_802 = l_Lean_scientificLitKind;
x_803 = lean_name_eq(x_10, x_802);
if (x_803 == 0)
{
lean_object* x_804; uint8_t x_805; 
x_804 = l_Lean_charLitKind;
x_805 = lean_name_eq(x_10, x_804);
if (x_805 == 0)
{
lean_object* x_806; uint8_t x_807; 
lean_dec(x_773);
x_806 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_807 = lean_name_eq(x_10, x_806);
if (x_807 == 0)
{
lean_object* x_808; uint8_t x_809; 
lean_dec(x_1);
x_808 = l_Lean_choiceKind;
x_809 = lean_name_eq(x_10, x_808);
lean_dec(x_10);
if (x_809 == 0)
{
lean_object* x_810; 
x_810 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_783);
lean_dec(x_2);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; 
x_811 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_812 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_811, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_783);
lean_dec(x_2);
return x_812;
}
}
else
{
lean_object* x_813; 
lean_dec(x_10);
lean_dec(x_2);
x_813 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_813;
}
}
else
{
lean_object* x_814; 
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_773)) {
 x_814 = lean_alloc_ctor(0, 2, 0);
} else {
 x_814 = x_773;
}
lean_ctor_set(x_814, 0, x_1);
lean_ctor_set(x_814, 1, x_772);
return x_814;
}
}
else
{
lean_object* x_815; 
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_773)) {
 x_815 = lean_alloc_ctor(0, 2, 0);
} else {
 x_815 = x_773;
}
lean_ctor_set(x_815, 0, x_1);
lean_ctor_set(x_815, 1, x_772);
return x_815;
}
}
else
{
lean_object* x_816; 
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_773)) {
 x_816 = lean_alloc_ctor(0, 2, 0);
} else {
 x_816 = x_773;
}
lean_ctor_set(x_816, 0, x_1);
lean_ctor_set(x_816, 1, x_772);
return x_816;
}
}
else
{
lean_object* x_817; 
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_773)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_773;
}
lean_ctor_set(x_817, 0, x_1);
lean_ctor_set(x_817, 1, x_772);
return x_817;
}
}
else
{
lean_object* x_818; 
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_773)) {
 x_818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_818 = x_773;
}
lean_ctor_set(x_818, 0, x_1);
lean_ctor_set(x_818, 1, x_772);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; 
lean_dec(x_773);
lean_dec(x_10);
x_819 = lean_unsigned_to_nat(0u);
x_820 = l_Lean_Syntax_getArg(x_1, x_819);
lean_inc(x_7);
lean_inc(x_820);
x_821 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_820, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_822 = lean_ctor_get(x_821, 1);
lean_inc(x_822);
lean_dec(x_821);
x_823 = lean_unsigned_to_nat(2u);
x_824 = l_Lean_Syntax_getArg(x_1, x_823);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_825 = x_1;
} else {
 lean_dec_ref(x_1);
 x_825 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_783);
x_826 = l_Lean_Elab_Term_CollectPatternVars_collect(x_824, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_822);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = l_Lean_Elab_Term_getCurrMacroScope(x_783, x_4, x_5, x_6, x_7, x_8, x_828);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_783);
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_832 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_831);
lean_dec(x_8);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_835 = x_832;
} else {
 lean_dec_ref(x_832);
 x_835 = lean_box(0);
}
x_836 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_837 = l_Lean_addMacroScope(x_833, x_836, x_830);
x_838 = l_Lean_instInhabitedSourceInfo___closed__1;
x_839 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_840 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_841 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_841, 0, x_838);
lean_ctor_set(x_841, 1, x_839);
lean_ctor_set(x_841, 2, x_837);
lean_ctor_set(x_841, 3, x_840);
x_842 = l_Array_empty___closed__1;
x_843 = lean_array_push(x_842, x_841);
x_844 = lean_array_push(x_842, x_820);
x_845 = lean_array_push(x_844, x_827);
x_846 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_825)) {
 x_847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_847 = x_825;
}
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_845);
x_848 = lean_array_push(x_843, x_847);
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_12);
lean_ctor_set(x_849, 1, x_848);
if (lean_is_scalar(x_835)) {
 x_850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_850 = x_835;
}
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_834);
return x_850;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_825);
lean_dec(x_820);
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_851 = lean_ctor_get(x_826, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_826, 1);
lean_inc(x_852);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_853 = x_826;
} else {
 lean_dec_ref(x_826);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(1, 2, 0);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_852);
return x_854;
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_820);
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_855 = lean_ctor_get(x_821, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_821, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_857 = x_821;
} else {
 lean_dec_ref(x_821);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_856);
return x_858;
}
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_773);
lean_dec(x_10);
x_859 = lean_unsigned_to_nat(0u);
x_860 = l_Lean_Syntax_getArg(x_1, x_859);
lean_dec(x_1);
x_861 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_862 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_861, x_860, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
return x_862;
}
}
else
{
lean_object* x_863; lean_object* x_864; uint8_t x_865; 
x_863 = l_Lean_instInhabitedSyntax;
x_864 = lean_array_get(x_863, x_11, x_768);
x_865 = l_Lean_Syntax_isNone(x_864);
if (x_865 == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; uint8_t x_870; 
lean_dec(x_773);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_866 = x_1;
} else {
 lean_dec_ref(x_1);
 x_866 = lean_box(0);
}
x_867 = lean_unsigned_to_nat(0u);
x_868 = l_Lean_Syntax_getArg(x_864, x_867);
x_869 = l_Lean_Syntax_getArg(x_864, x_768);
x_870 = l_Lean_Syntax_isNone(x_869);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_871 = l_Lean_Syntax_getArg(x_869, x_867);
lean_inc(x_871);
x_872 = l_Lean_Syntax_getKind(x_871);
x_873 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_874 = lean_name_eq(x_872, x_873);
lean_dec(x_872);
if (x_874 == 0)
{
lean_object* x_875; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_783);
lean_inc(x_2);
x_875 = l_Lean_Elab_Term_CollectPatternVars_collect(x_868, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = l_Lean_Syntax_setArg(x_864, x_867, x_876);
x_879 = l_Lean_Syntax_getArg(x_871, x_768);
x_880 = l_Lean_Syntax_getArgs(x_879);
lean_dec(x_879);
x_881 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_882 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_880, x_881, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_877);
lean_dec(x_880);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_885 = x_882;
} else {
 lean_dec_ref(x_882);
 x_885 = lean_box(0);
}
x_886 = l_Lean_nullKind;
if (lean_is_scalar(x_866)) {
 x_887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_887 = x_866;
}
lean_ctor_set(x_887, 0, x_886);
lean_ctor_set(x_887, 1, x_883);
x_888 = l_Lean_Syntax_setArg(x_871, x_768, x_887);
x_889 = l_Lean_Syntax_setArg(x_869, x_867, x_888);
x_890 = l_Lean_Syntax_setArg(x_878, x_768, x_889);
x_891 = lean_array_set(x_11, x_768, x_890);
x_892 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_892, 0, x_10);
lean_ctor_set(x_892, 1, x_891);
if (lean_is_scalar(x_885)) {
 x_893 = lean_alloc_ctor(0, 2, 0);
} else {
 x_893 = x_885;
}
lean_ctor_set(x_893, 0, x_892);
lean_ctor_set(x_893, 1, x_884);
return x_893;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
lean_dec(x_878);
lean_dec(x_871);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_11);
lean_dec(x_10);
x_894 = lean_ctor_get(x_882, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_882, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_896 = x_882;
} else {
 lean_dec_ref(x_882);
 x_896 = lean_box(0);
}
if (lean_is_scalar(x_896)) {
 x_897 = lean_alloc_ctor(1, 2, 0);
} else {
 x_897 = x_896;
}
lean_ctor_set(x_897, 0, x_894);
lean_ctor_set(x_897, 1, x_895);
return x_897;
}
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_871);
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_898 = lean_ctor_get(x_875, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_875, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_900 = x_875;
} else {
 lean_dec_ref(x_875);
 x_900 = lean_box(0);
}
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(1, 2, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_898);
lean_ctor_set(x_901, 1, x_899);
return x_901;
}
}
else
{
lean_object* x_902; 
lean_dec(x_871);
lean_dec(x_869);
x_902 = l_Lean_Elab_Term_CollectPatternVars_collect(x_868, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_905 = x_902;
} else {
 lean_dec_ref(x_902);
 x_905 = lean_box(0);
}
x_906 = l_Lean_Syntax_setArg(x_864, x_867, x_903);
x_907 = lean_array_set(x_11, x_768, x_906);
if (lean_is_scalar(x_866)) {
 x_908 = lean_alloc_ctor(1, 2, 0);
} else {
 x_908 = x_866;
}
lean_ctor_set(x_908, 0, x_10);
lean_ctor_set(x_908, 1, x_907);
if (lean_is_scalar(x_905)) {
 x_909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_909 = x_905;
}
lean_ctor_set(x_909, 0, x_908);
lean_ctor_set(x_909, 1, x_904);
return x_909;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_11);
lean_dec(x_10);
x_910 = lean_ctor_get(x_902, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_902, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_912 = x_902;
} else {
 lean_dec_ref(x_902);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_910);
lean_ctor_set(x_913, 1, x_911);
return x_913;
}
}
}
else
{
lean_object* x_914; 
lean_dec(x_869);
x_914 = l_Lean_Elab_Term_CollectPatternVars_collect(x_868, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_917 = x_914;
} else {
 lean_dec_ref(x_914);
 x_917 = lean_box(0);
}
x_918 = l_Lean_Syntax_setArg(x_864, x_867, x_915);
x_919 = lean_array_set(x_11, x_768, x_918);
if (lean_is_scalar(x_866)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_866;
}
lean_ctor_set(x_920, 0, x_10);
lean_ctor_set(x_920, 1, x_919);
if (lean_is_scalar(x_917)) {
 x_921 = lean_alloc_ctor(0, 2, 0);
} else {
 x_921 = x_917;
}
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_916);
return x_921;
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_866);
lean_dec(x_864);
lean_dec(x_11);
lean_dec(x_10);
x_922 = lean_ctor_get(x_914, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_914, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_924 = x_914;
} else {
 lean_dec_ref(x_914);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 2, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_922);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
}
else
{
lean_object* x_926; 
lean_dec(x_864);
lean_dec(x_783);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_773)) {
 x_926 = lean_alloc_ctor(0, 2, 0);
} else {
 x_926 = x_773;
}
lean_ctor_set(x_926, 0, x_1);
lean_ctor_set(x_926, 1, x_772);
return x_926;
}
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec(x_783);
lean_dec(x_773);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_927 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_772);
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = lean_st_ref_get(x_8, x_929);
lean_dec(x_8);
x_931 = lean_ctor_get(x_930, 1);
lean_inc(x_931);
lean_dec(x_930);
x_932 = lean_st_ref_take(x_2, x_931);
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
x_935 = lean_ctor_get(x_933, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_933, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_933)) {
 lean_ctor_release(x_933, 0);
 lean_ctor_release(x_933, 1);
 x_937 = x_933;
} else {
 lean_dec_ref(x_933);
 x_937 = lean_box(0);
}
x_938 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_928);
x_939 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_939, 0, x_938);
x_940 = lean_array_push(x_936, x_939);
if (lean_is_scalar(x_937)) {
 x_941 = lean_alloc_ctor(0, 2, 0);
} else {
 x_941 = x_937;
}
lean_ctor_set(x_941, 0, x_935);
lean_ctor_set(x_941, 1, x_940);
x_942 = lean_st_ref_set(x_2, x_941, x_934);
lean_dec(x_2);
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_944 = x_942;
} else {
 lean_dec_ref(x_942);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(0, 2, 0);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_928);
lean_ctor_set(x_945, 1, x_943);
return x_945;
}
}
else
{
lean_object* x_946; lean_object* x_947; uint8_t x_948; 
lean_dec(x_773);
lean_dec(x_1);
x_946 = l_Lean_instInhabitedSyntax;
x_947 = lean_array_get(x_946, x_11, x_768);
x_948 = l_Lean_Syntax_isNone(x_947);
if (x_948 == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_11);
lean_dec(x_10);
x_949 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_950 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_947, x_949, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_783);
lean_dec(x_2);
lean_dec(x_947);
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_953 = x_950;
} else {
 lean_dec_ref(x_950);
 x_953 = lean_box(0);
}
if (lean_is_scalar(x_953)) {
 x_954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_954 = x_953;
}
lean_ctor_set(x_954, 0, x_951);
lean_ctor_set(x_954, 1, x_952);
return x_954;
}
else
{
lean_object* x_955; lean_object* x_956; 
lean_dec(x_947);
x_955 = lean_box(0);
x_956 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_955, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
return x_956;
}
}
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_773);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_957 = x_1;
} else {
 lean_dec_ref(x_1);
 x_957 = lean_box(0);
}
x_958 = l_Lean_instInhabitedSyntax;
x_959 = lean_array_get(x_958, x_11, x_768);
x_960 = l_Lean_Syntax_getArgs(x_959);
lean_dec(x_959);
x_961 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_962 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_960, x_961, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_960);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_965 = x_962;
} else {
 lean_dec_ref(x_962);
 x_965 = lean_box(0);
}
x_966 = l_Lean_nullKind;
if (lean_is_scalar(x_957)) {
 x_967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_967 = x_957;
}
lean_ctor_set(x_967, 0, x_966);
lean_ctor_set(x_967, 1, x_963);
x_968 = lean_array_set(x_11, x_768, x_967);
x_969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_969, 0, x_10);
lean_ctor_set(x_969, 1, x_968);
if (lean_is_scalar(x_965)) {
 x_970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_970 = x_965;
}
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_964);
return x_970;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_957);
lean_dec(x_11);
lean_dec(x_10);
x_971 = lean_ctor_get(x_962, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_962, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_973 = x_962;
} else {
 lean_dec_ref(x_962);
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
lean_object* x_975; lean_object* x_976; 
lean_dec(x_773);
lean_dec(x_11);
lean_dec(x_10);
x_975 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_976 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_975, x_1, x_2, x_783, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_1);
return x_976;
}
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; uint8_t x_1004; uint8_t x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_977 = lean_ctor_get(x_7, 0);
x_978 = lean_ctor_get(x_7, 1);
x_979 = lean_ctor_get(x_7, 2);
x_980 = lean_ctor_get(x_7, 3);
x_981 = lean_ctor_get(x_7, 4);
x_982 = lean_ctor_get(x_7, 5);
lean_inc(x_982);
lean_inc(x_981);
lean_inc(x_980);
lean_inc(x_979);
lean_inc(x_978);
lean_inc(x_977);
lean_dec(x_7);
x_983 = l_Lean_replaceRef(x_1, x_980);
lean_dec(x_980);
x_984 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_984, 0, x_977);
lean_ctor_set(x_984, 1, x_978);
lean_ctor_set(x_984, 2, x_979);
lean_ctor_set(x_984, 3, x_983);
lean_ctor_set(x_984, 4, x_981);
lean_ctor_set(x_984, 5, x_982);
x_985 = lean_st_ref_take(x_8, x_9);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec(x_985);
x_988 = lean_ctor_get(x_986, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_986, 1);
lean_inc(x_989);
x_990 = lean_ctor_get(x_986, 2);
lean_inc(x_990);
x_991 = lean_ctor_get(x_986, 3);
lean_inc(x_991);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 lean_ctor_release(x_986, 2);
 lean_ctor_release(x_986, 3);
 x_992 = x_986;
} else {
 lean_dec_ref(x_986);
 x_992 = lean_box(0);
}
x_993 = lean_unsigned_to_nat(1u);
x_994 = lean_nat_add(x_989, x_993);
if (lean_is_scalar(x_992)) {
 x_995 = lean_alloc_ctor(0, 4, 0);
} else {
 x_995 = x_992;
}
lean_ctor_set(x_995, 0, x_988);
lean_ctor_set(x_995, 1, x_994);
lean_ctor_set(x_995, 2, x_990);
lean_ctor_set(x_995, 3, x_991);
x_996 = lean_st_ref_set(x_8, x_995, x_987);
x_997 = lean_ctor_get(x_996, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_996)) {
 lean_ctor_release(x_996, 0);
 lean_ctor_release(x_996, 1);
 x_998 = x_996;
} else {
 lean_dec_ref(x_996);
 x_998 = lean_box(0);
}
x_999 = lean_ctor_get(x_3, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_3, 1);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_3, 2);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_3, 3);
lean_inc(x_1002);
x_1003 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_1004 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_1005 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_1006 = lean_ctor_get(x_3, 5);
lean_inc(x_1006);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_1007 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1007 = lean_box(0);
}
if (lean_is_scalar(x_1007)) {
 x_1008 = lean_alloc_ctor(0, 6, 3);
} else {
 x_1008 = x_1007;
}
lean_ctor_set(x_1008, 0, x_999);
lean_ctor_set(x_1008, 1, x_1000);
lean_ctor_set(x_1008, 2, x_1001);
lean_ctor_set(x_1008, 3, x_1002);
lean_ctor_set(x_1008, 4, x_989);
lean_ctor_set(x_1008, 5, x_1006);
lean_ctor_set_uint8(x_1008, sizeof(void*)*6, x_1003);
lean_ctor_set_uint8(x_1008, sizeof(void*)*6 + 1, x_1004);
lean_ctor_set_uint8(x_1008, sizeof(void*)*6 + 2, x_1005);
if (x_14 == 0)
{
lean_object* x_1009; uint8_t x_1010; 
x_1009 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_1010 = lean_name_eq(x_10, x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; uint8_t x_1012; 
x_1011 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_261____closed__2;
x_1012 = lean_name_eq(x_10, x_1011);
if (x_1012 == 0)
{
lean_object* x_1013; uint8_t x_1014; 
x_1013 = l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
x_1014 = lean_name_eq(x_10, x_1013);
if (x_1014 == 0)
{
lean_object* x_1015; uint8_t x_1016; 
x_1015 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
x_1016 = lean_name_eq(x_10, x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; uint8_t x_1018; 
lean_dec(x_11);
x_1017 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_1018 = lean_name_eq(x_10, x_1017);
if (x_1018 == 0)
{
lean_object* x_1019; uint8_t x_1020; 
x_1019 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_1020 = lean_name_eq(x_10, x_1019);
if (x_1020 == 0)
{
lean_object* x_1021; uint8_t x_1022; 
x_1021 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
x_1022 = lean_name_eq(x_10, x_1021);
if (x_1022 == 0)
{
lean_object* x_1023; uint8_t x_1024; 
x_1023 = l_Lean_strLitKind;
x_1024 = lean_name_eq(x_10, x_1023);
if (x_1024 == 0)
{
lean_object* x_1025; uint8_t x_1026; 
x_1025 = l_Lean_numLitKind;
x_1026 = lean_name_eq(x_10, x_1025);
if (x_1026 == 0)
{
lean_object* x_1027; uint8_t x_1028; 
x_1027 = l_Lean_scientificLitKind;
x_1028 = lean_name_eq(x_10, x_1027);
if (x_1028 == 0)
{
lean_object* x_1029; uint8_t x_1030; 
x_1029 = l_Lean_charLitKind;
x_1030 = lean_name_eq(x_10, x_1029);
if (x_1030 == 0)
{
lean_object* x_1031; uint8_t x_1032; 
lean_dec(x_998);
x_1031 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_1032 = lean_name_eq(x_10, x_1031);
if (x_1032 == 0)
{
lean_object* x_1033; uint8_t x_1034; 
lean_dec(x_1);
x_1033 = l_Lean_choiceKind;
x_1034 = lean_name_eq(x_10, x_1033);
lean_dec(x_10);
if (x_1034 == 0)
{
lean_object* x_1035; 
x_1035 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
lean_dec(x_8);
lean_dec(x_984);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1008);
lean_dec(x_2);
return x_1035;
}
else
{
lean_object* x_1036; lean_object* x_1037; 
x_1036 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_1037 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_1036, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
lean_dec(x_8);
lean_dec(x_984);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1008);
lean_dec(x_2);
return x_1037;
}
}
else
{
lean_object* x_1038; 
lean_dec(x_10);
lean_dec(x_2);
x_1038 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(x_1, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
lean_dec(x_8);
lean_dec(x_984);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_1038;
}
}
else
{
lean_object* x_1039; 
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_998)) {
 x_1039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1039 = x_998;
}
lean_ctor_set(x_1039, 0, x_1);
lean_ctor_set(x_1039, 1, x_997);
return x_1039;
}
}
else
{
lean_object* x_1040; 
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_998)) {
 x_1040 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1040 = x_998;
}
lean_ctor_set(x_1040, 0, x_1);
lean_ctor_set(x_1040, 1, x_997);
return x_1040;
}
}
else
{
lean_object* x_1041; 
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_998)) {
 x_1041 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1041 = x_998;
}
lean_ctor_set(x_1041, 0, x_1);
lean_ctor_set(x_1041, 1, x_997);
return x_1041;
}
}
else
{
lean_object* x_1042; 
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_998)) {
 x_1042 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1042 = x_998;
}
lean_ctor_set(x_1042, 0, x_1);
lean_ctor_set(x_1042, 1, x_997);
return x_1042;
}
}
else
{
lean_object* x_1043; 
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_998)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_998;
}
lean_ctor_set(x_1043, 0, x_1);
lean_ctor_set(x_1043, 1, x_997);
return x_1043;
}
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_998);
lean_dec(x_10);
x_1044 = lean_unsigned_to_nat(0u);
x_1045 = l_Lean_Syntax_getArg(x_1, x_1044);
lean_inc(x_984);
lean_inc(x_1045);
x_1046 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1045, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1047 = lean_ctor_get(x_1046, 1);
lean_inc(x_1047);
lean_dec(x_1046);
x_1048 = lean_unsigned_to_nat(2u);
x_1049 = l_Lean_Syntax_getArg(x_1, x_1048);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1050 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1050 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_984);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1008);
x_1051 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1049, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_1047);
if (lean_obj_tag(x_1051) == 0)
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
lean_dec(x_1051);
x_1054 = l_Lean_Elab_Term_getCurrMacroScope(x_1008, x_4, x_5, x_6, x_984, x_8, x_1053);
lean_dec(x_984);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1008);
x_1055 = lean_ctor_get(x_1054, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1054, 1);
lean_inc(x_1056);
lean_dec(x_1054);
x_1057 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1056);
lean_dec(x_8);
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1057)) {
 lean_ctor_release(x_1057, 0);
 lean_ctor_release(x_1057, 1);
 x_1060 = x_1057;
} else {
 lean_dec_ref(x_1057);
 x_1060 = lean_box(0);
}
x_1061 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_1062 = l_Lean_addMacroScope(x_1058, x_1061, x_1055);
x_1063 = l_Lean_instInhabitedSourceInfo___closed__1;
x_1064 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_1065 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_1066 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1066, 0, x_1063);
lean_ctor_set(x_1066, 1, x_1064);
lean_ctor_set(x_1066, 2, x_1062);
lean_ctor_set(x_1066, 3, x_1065);
x_1067 = l_Array_empty___closed__1;
x_1068 = lean_array_push(x_1067, x_1066);
x_1069 = lean_array_push(x_1067, x_1045);
x_1070 = lean_array_push(x_1069, x_1052);
x_1071 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_1050)) {
 x_1072 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1072 = x_1050;
}
lean_ctor_set(x_1072, 0, x_1071);
lean_ctor_set(x_1072, 1, x_1070);
x_1073 = lean_array_push(x_1068, x_1072);
x_1074 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1074, 0, x_12);
lean_ctor_set(x_1074, 1, x_1073);
if (lean_is_scalar(x_1060)) {
 x_1075 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1075 = x_1060;
}
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1059);
return x_1075;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_1050);
lean_dec(x_1045);
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1076 = lean_ctor_get(x_1051, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1051, 1);
lean_inc(x_1077);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1078 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1078 = lean_box(0);
}
if (lean_is_scalar(x_1078)) {
 x_1079 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1079 = x_1078;
}
lean_ctor_set(x_1079, 0, x_1076);
lean_ctor_set(x_1079, 1, x_1077);
return x_1079;
}
}
else
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
lean_dec(x_1045);
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1080 = lean_ctor_get(x_1046, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1046, 1);
lean_inc(x_1081);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1082 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1082 = lean_box(0);
}
if (lean_is_scalar(x_1082)) {
 x_1083 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1083 = x_1082;
}
lean_ctor_set(x_1083, 0, x_1080);
lean_ctor_set(x_1083, 1, x_1081);
return x_1083;
}
}
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_998);
lean_dec(x_10);
x_1084 = lean_unsigned_to_nat(0u);
x_1085 = l_Lean_Syntax_getArg(x_1, x_1084);
lean_dec(x_1);
x_1086 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1087 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1086, x_1085, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
return x_1087;
}
}
else
{
lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; 
x_1088 = l_Lean_instInhabitedSyntax;
x_1089 = lean_array_get(x_1088, x_11, x_993);
x_1090 = l_Lean_Syntax_isNone(x_1089);
if (x_1090 == 0)
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; 
lean_dec(x_998);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1091 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1091 = lean_box(0);
}
x_1092 = lean_unsigned_to_nat(0u);
x_1093 = l_Lean_Syntax_getArg(x_1089, x_1092);
x_1094 = l_Lean_Syntax_getArg(x_1089, x_993);
x_1095 = l_Lean_Syntax_isNone(x_1094);
if (x_1095 == 0)
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; uint8_t x_1099; 
x_1096 = l_Lean_Syntax_getArg(x_1094, x_1092);
lean_inc(x_1096);
x_1097 = l_Lean_Syntax_getKind(x_1096);
x_1098 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_1099 = lean_name_eq(x_1097, x_1098);
lean_dec(x_1097);
if (x_1099 == 0)
{
lean_object* x_1100; 
lean_inc(x_8);
lean_inc(x_984);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1008);
lean_inc(x_2);
x_1100 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1093, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = l_Lean_Syntax_setArg(x_1089, x_1092, x_1101);
x_1104 = l_Lean_Syntax_getArg(x_1096, x_993);
x_1105 = l_Lean_Syntax_getArgs(x_1104);
lean_dec(x_1104);
x_1106 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1107 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_1105, x_1106, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_1102);
lean_dec(x_1105);
if (lean_obj_tag(x_1107) == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1108 = lean_ctor_get(x_1107, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1107, 1);
lean_inc(x_1109);
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 lean_ctor_release(x_1107, 1);
 x_1110 = x_1107;
} else {
 lean_dec_ref(x_1107);
 x_1110 = lean_box(0);
}
x_1111 = l_Lean_nullKind;
if (lean_is_scalar(x_1091)) {
 x_1112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1112 = x_1091;
}
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_1108);
x_1113 = l_Lean_Syntax_setArg(x_1096, x_993, x_1112);
x_1114 = l_Lean_Syntax_setArg(x_1094, x_1092, x_1113);
x_1115 = l_Lean_Syntax_setArg(x_1103, x_993, x_1114);
x_1116 = lean_array_set(x_11, x_993, x_1115);
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_10);
lean_ctor_set(x_1117, 1, x_1116);
if (lean_is_scalar(x_1110)) {
 x_1118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1118 = x_1110;
}
lean_ctor_set(x_1118, 0, x_1117);
lean_ctor_set(x_1118, 1, x_1109);
return x_1118;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec(x_1103);
lean_dec(x_1096);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_11);
lean_dec(x_10);
x_1119 = lean_ctor_get(x_1107, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1107, 1);
lean_inc(x_1120);
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 lean_ctor_release(x_1107, 1);
 x_1121 = x_1107;
} else {
 lean_dec_ref(x_1107);
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
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_1096);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1089);
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1123 = lean_ctor_get(x_1100, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1100, 1);
lean_inc(x_1124);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 x_1125 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1123);
lean_ctor_set(x_1126, 1, x_1124);
return x_1126;
}
}
else
{
lean_object* x_1127; 
lean_dec(x_1096);
lean_dec(x_1094);
x_1127 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1093, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1127, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1127)) {
 lean_ctor_release(x_1127, 0);
 lean_ctor_release(x_1127, 1);
 x_1130 = x_1127;
} else {
 lean_dec_ref(x_1127);
 x_1130 = lean_box(0);
}
x_1131 = l_Lean_Syntax_setArg(x_1089, x_1092, x_1128);
x_1132 = lean_array_set(x_11, x_993, x_1131);
if (lean_is_scalar(x_1091)) {
 x_1133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1133 = x_1091;
}
lean_ctor_set(x_1133, 0, x_10);
lean_ctor_set(x_1133, 1, x_1132);
if (lean_is_scalar(x_1130)) {
 x_1134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1134 = x_1130;
}
lean_ctor_set(x_1134, 0, x_1133);
lean_ctor_set(x_1134, 1, x_1129);
return x_1134;
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
lean_dec(x_1091);
lean_dec(x_1089);
lean_dec(x_11);
lean_dec(x_10);
x_1135 = lean_ctor_get(x_1127, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1127, 1);
lean_inc(x_1136);
if (lean_is_exclusive(x_1127)) {
 lean_ctor_release(x_1127, 0);
 lean_ctor_release(x_1127, 1);
 x_1137 = x_1127;
} else {
 lean_dec_ref(x_1127);
 x_1137 = lean_box(0);
}
if (lean_is_scalar(x_1137)) {
 x_1138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1138 = x_1137;
}
lean_ctor_set(x_1138, 0, x_1135);
lean_ctor_set(x_1138, 1, x_1136);
return x_1138;
}
}
}
else
{
lean_object* x_1139; 
lean_dec(x_1094);
x_1139 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1093, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
if (lean_obj_tag(x_1139) == 0)
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1140 = lean_ctor_get(x_1139, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1139, 1);
lean_inc(x_1141);
if (lean_is_exclusive(x_1139)) {
 lean_ctor_release(x_1139, 0);
 lean_ctor_release(x_1139, 1);
 x_1142 = x_1139;
} else {
 lean_dec_ref(x_1139);
 x_1142 = lean_box(0);
}
x_1143 = l_Lean_Syntax_setArg(x_1089, x_1092, x_1140);
x_1144 = lean_array_set(x_11, x_993, x_1143);
if (lean_is_scalar(x_1091)) {
 x_1145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1145 = x_1091;
}
lean_ctor_set(x_1145, 0, x_10);
lean_ctor_set(x_1145, 1, x_1144);
if (lean_is_scalar(x_1142)) {
 x_1146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1146 = x_1142;
}
lean_ctor_set(x_1146, 0, x_1145);
lean_ctor_set(x_1146, 1, x_1141);
return x_1146;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1091);
lean_dec(x_1089);
lean_dec(x_11);
lean_dec(x_10);
x_1147 = lean_ctor_get(x_1139, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1139, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1139)) {
 lean_ctor_release(x_1139, 0);
 lean_ctor_release(x_1139, 1);
 x_1149 = x_1139;
} else {
 lean_dec_ref(x_1139);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1147);
lean_ctor_set(x_1150, 1, x_1148);
return x_1150;
}
}
}
else
{
lean_object* x_1151; 
lean_dec(x_1089);
lean_dec(x_1008);
lean_dec(x_984);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_998)) {
 x_1151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1151 = x_998;
}
lean_ctor_set(x_1151, 0, x_1);
lean_ctor_set(x_1151, 1, x_997);
return x_1151;
}
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
lean_dec(x_1008);
lean_dec(x_998);
lean_dec(x_984);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1152 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_mkMVarSyntax___rarg(x_8, x_997);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_st_ref_get(x_8, x_1154);
lean_dec(x_8);
x_1156 = lean_ctor_get(x_1155, 1);
lean_inc(x_1156);
lean_dec(x_1155);
x_1157 = lean_st_ref_take(x_2, x_1156);
x_1158 = lean_ctor_get(x_1157, 0);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1157, 1);
lean_inc(x_1159);
lean_dec(x_1157);
x_1160 = lean_ctor_get(x_1158, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1158, 1);
lean_inc(x_1161);
if (lean_is_exclusive(x_1158)) {
 lean_ctor_release(x_1158, 0);
 lean_ctor_release(x_1158, 1);
 x_1162 = x_1158;
} else {
 lean_dec_ref(x_1158);
 x_1162 = lean_box(0);
}
x_1163 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMVarSyntaxMVarId(x_1153);
x_1164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1164, 0, x_1163);
x_1165 = lean_array_push(x_1161, x_1164);
if (lean_is_scalar(x_1162)) {
 x_1166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1166 = x_1162;
}
lean_ctor_set(x_1166, 0, x_1160);
lean_ctor_set(x_1166, 1, x_1165);
x_1167 = lean_st_ref_set(x_2, x_1166, x_1159);
lean_dec(x_2);
x_1168 = lean_ctor_get(x_1167, 1);
lean_inc(x_1168);
if (lean_is_exclusive(x_1167)) {
 lean_ctor_release(x_1167, 0);
 lean_ctor_release(x_1167, 1);
 x_1169 = x_1167;
} else {
 lean_dec_ref(x_1167);
 x_1169 = lean_box(0);
}
if (lean_is_scalar(x_1169)) {
 x_1170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1170 = x_1169;
}
lean_ctor_set(x_1170, 0, x_1153);
lean_ctor_set(x_1170, 1, x_1168);
return x_1170;
}
}
else
{
lean_object* x_1171; lean_object* x_1172; uint8_t x_1173; 
lean_dec(x_998);
lean_dec(x_1);
x_1171 = l_Lean_instInhabitedSyntax;
x_1172 = lean_array_get(x_1171, x_11, x_993);
x_1173 = l_Lean_Syntax_isNone(x_1172);
if (x_1173 == 0)
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
lean_dec(x_11);
lean_dec(x_10);
x_1174 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_1175 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_1172, x_1174, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1008);
lean_dec(x_2);
lean_dec(x_1172);
x_1176 = lean_ctor_get(x_1175, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1175, 1);
lean_inc(x_1177);
if (lean_is_exclusive(x_1175)) {
 lean_ctor_release(x_1175, 0);
 lean_ctor_release(x_1175, 1);
 x_1178 = x_1175;
} else {
 lean_dec_ref(x_1175);
 x_1178 = lean_box(0);
}
if (lean_is_scalar(x_1178)) {
 x_1179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1179 = x_1178;
}
lean_ctor_set(x_1179, 0, x_1176);
lean_ctor_set(x_1179, 1, x_1177);
return x_1179;
}
else
{
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_1172);
x_1180 = lean_box(0);
x_1181 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_11, x_10, x_1180, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
return x_1181;
}
}
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
lean_dec(x_998);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1182 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1182 = lean_box(0);
}
x_1183 = l_Lean_instInhabitedSyntax;
x_1184 = lean_array_get(x_1183, x_11, x_993);
x_1185 = l_Lean_Syntax_getArgs(x_1184);
lean_dec(x_1184);
x_1186 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1187 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_1185, x_1186, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
lean_dec(x_1185);
if (lean_obj_tag(x_1187) == 0)
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1188 = lean_ctor_get(x_1187, 0);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_1187, 1);
lean_inc(x_1189);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 lean_ctor_release(x_1187, 1);
 x_1190 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1190 = lean_box(0);
}
x_1191 = l_Lean_nullKind;
if (lean_is_scalar(x_1182)) {
 x_1192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1192 = x_1182;
}
lean_ctor_set(x_1192, 0, x_1191);
lean_ctor_set(x_1192, 1, x_1188);
x_1193 = lean_array_set(x_11, x_993, x_1192);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_10);
lean_ctor_set(x_1194, 1, x_1193);
if (lean_is_scalar(x_1190)) {
 x_1195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1195 = x_1190;
}
lean_ctor_set(x_1195, 0, x_1194);
lean_ctor_set(x_1195, 1, x_1189);
return x_1195;
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1182);
lean_dec(x_11);
lean_dec(x_10);
x_1196 = lean_ctor_get(x_1187, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1187, 1);
lean_inc(x_1197);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 lean_ctor_release(x_1187, 1);
 x_1198 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1198 = lean_box(0);
}
if (lean_is_scalar(x_1198)) {
 x_1199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1199 = x_1198;
}
lean_ctor_set(x_1199, 0, x_1196);
lean_ctor_set(x_1199, 1, x_1197);
return x_1199;
}
}
}
else
{
lean_object* x_1200; lean_object* x_1201; 
lean_dec(x_998);
lean_dec(x_11);
lean_dec(x_10);
x_1200 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1201 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_1200, x_1, x_2, x_1008, x_4, x_5, x_6, x_984, x_8, x_997);
lean_dec(x_1);
return x_1201;
}
}
}
}
case 3:
{
lean_object* x_1205; lean_object* x_1206; 
x_1205 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_1206 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_processId(x_1205, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1206;
}
default: 
{
lean_object* x_1207; 
lean_dec(x_1);
x_1207 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1207;
}
}
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_61 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_73 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(x_69, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
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
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_46);
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
x_14 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_21 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_20);
x_23 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_finalize___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_10);
lean_dec(x_22);
return x_23;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2___rarg), 1, 0);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_73 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2___rarg(x_41);
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
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__3(x_1, x_10, x_11, x_18, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__3(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkFVar(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Meta_inferType(x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_7);
x_23 = l_Lean_Meta_mkFreshExprMVarWithId(x_14, x_20, x_21, x_22, x_7, x_8, x_9, x_10, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = x_2 + x_25;
x_27 = lean_box(0);
x_2 = x_26;
x_4 = x_27;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = 1;
x_34 = x_2 + x_33;
x_35 = lean_box(0);
x_2 = x_34;
x_4 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_11);
return x_37;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_array_get_size(x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(x_4, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 0;
x_33 = lean_box(0);
lean_inc(x_7);
x_34 = l_Lean_Meta_mkFreshTypeMVar(x_32, x_33, x_7, x_8, x_9, x_10, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_37, 0, x_3);
lean_closure_set(x_37, 1, x_4);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_2);
x_38 = 0;
x_39 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_31, x_38, x_35, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = 0;
x_42 = lean_box(0);
lean_inc(x_7);
x_43 = l_Lean_Meta_mkFreshTypeMVar(x_41, x_42, x_7, x_8, x_9, x_10, x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_5);
x_46 = l_Lean_Elab_Term_mkFreshBinderName(x_5, x_6, x_7, x_8, x_9, x_10, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___rarg___lambda__2___boxed), 13, 5);
lean_closure_set(x_49, 0, x_3);
lean_closure_set(x_49, 1, x_40);
lean_closure_set(x_49, 2, x_4);
lean_closure_set(x_49, 3, x_1);
lean_closure_set(x_49, 4, x_2);
x_50 = 0;
x_51 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_47, x_50, x_44, x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
return x_51;
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Match_0__Lean_Elab_Term_withPatternVars_loop___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
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
x_122 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_88 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_59 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_111 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_box(0);
x_18 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_16, x_1, x_17);
lean_ctor_set(x_13, 0, x_18);
x_19 = lean_st_ref_set(x_2, x_13, x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_24, x_1, x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
x_30 = lean_st_ref_set(x_2, x_29, x_14);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_31);
return x_33;
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
lean_inc(x_10);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_41, 0, x_1);
x_42 = lean_array_get_size(x_39);
x_43 = l_Array_findIdx_x3f_loop___rarg(x_39, x_41, x_42, x_30, lean_box(0));
x_44 = lean_box(0);
lean_inc(x_19);
x_45 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_19, x_44);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_array_push(x_39, x_32);
lean_ctor_set(x_36, 2, x_45);
lean_ctor_set(x_36, 1, x_46);
x_47 = lean_st_ref_set(x_2, x_36, x_37);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_19);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
lean_dec(x_43);
x_55 = l_Array_insertAt___rarg(x_39, x_54, x_32);
lean_dec(x_54);
lean_ctor_set(x_36, 2, x_45);
lean_ctor_set(x_36, 1, x_55);
x_56 = lean_st_ref_set(x_2, x_36, x_37);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_19);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_19);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_36, 0);
x_64 = lean_ctor_get(x_36, 1);
x_65 = lean_ctor_get(x_36, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_36);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_mkLocalDeclFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_66, 0, x_1);
x_67 = lean_array_get_size(x_64);
x_68 = l_Array_findIdx_x3f_loop___rarg(x_64, x_66, x_67, x_30, lean_box(0));
x_69 = lean_box(0);
lean_inc(x_19);
x_70 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_65, x_19, x_69);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_array_push(x_64, x_32);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_70);
x_73 = lean_st_ref_set(x_2, x_72, x_37);
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
lean_ctor_set(x_76, 0, x_19);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
lean_dec(x_68);
x_79 = l_Array_insertAt___rarg(x_64, x_78, x_32);
lean_dec(x_78);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_63);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_70);
x_81 = lean_st_ref_set(x_2, x_80, x_37);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_19);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_21);
if (x_86 == 0)
{
return x_21;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_21, 0);
x_88 = lean_ctor_get(x_21, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_15);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_15, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_16, 0);
lean_inc(x_92);
lean_dec(x_16);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_15, 0, x_93);
return x_15;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_15, 1);
lean_inc(x_94);
lean_dec(x_15);
x_95 = lean_ctor_get(x_16, 0);
lean_inc(x_95);
lean_dec(x_16);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
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
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_LocalDecl_fvarId(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_37 = l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_LocalDecl_fvarId(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
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
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_62 = l_Lean_Expr_fvarId_x21(x_1);
x_73 = lean_st_ref_get(x_8, x_9);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_get(x_2, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_nat_dec_lt(x_80, x_79);
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_79);
lean_dec(x_78);
x_82 = 0;
x_63 = x_82;
x_64 = x_77;
goto block_72;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_79, x_79);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_79);
lean_dec(x_78);
x_84 = 0;
x_63 = x_84;
x_64 = x_77;
goto block_72;
}
else
{
size_t x_85; size_t x_86; uint8_t x_87; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_87 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(x_62, x_78, x_85, x_86);
lean_dec(x_78);
x_63 = x_87;
x_64 = x_77;
goto block_72;
}
}
block_72:
{
if (x_63 == 0)
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_62);
x_65 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_Elab_Term_ToDepElimPattern_main___lambda__2(x_62, x_1, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_71;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_9);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Lean_Expr_getAppNumArgsAux(x_1, x_94);
x_96 = lean_unsigned_to_nat(2u);
x_97 = lean_nat_sub(x_95, x_96);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_97);
x_100 = l_Lean_Expr_getRevArg_x21(x_1, x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_101 = l_Lean_Elab_Term_ToDepElimPattern_main(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
x_105 = lean_nat_sub(x_95, x_98);
lean_dec(x_95);
x_106 = lean_nat_sub(x_105, x_98);
lean_dec(x_105);
x_107 = l_Lean_Expr_getRevArg_x21(x_1, x_106);
lean_dec(x_1);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_101, 0, x_109);
return x_101;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_107);
lean_free_object(x_101);
lean_dec(x_103);
x_110 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
x_111 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_101, 0);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_101);
x_114 = lean_nat_sub(x_95, x_98);
lean_dec(x_95);
x_115 = lean_nat_sub(x_114, x_98);
lean_dec(x_114);
x_116 = l_Lean_Expr_getRevArg_x21(x_1, x_115);
lean_dec(x_1);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_116);
lean_dec(x_112);
x_120 = l_Lean_Elab_Term_ToDepElimPattern_main___closed__3;
x_121 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_113);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_101);
if (x_122 == 0)
{
return x_101;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_101, 0);
x_124 = lean_ctor_get(x_101, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_101);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_1);
x_126 = lean_ctor_get(x_11, 0);
lean_inc(x_126);
lean_dec(x_11);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_List_mapM___at_Lean_Elab_Term_ToDepElimPattern_main___spec__4(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_129, 0, x_132);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_129, 0);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_129);
x_135 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
uint8_t x_137; 
lean_dec(x_127);
x_137 = !lean_is_exclusive(x_129);
if (x_137 == 0)
{
return x_129;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_129, 0);
x_139 = lean_ctor_get(x_129, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_129);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
lean_object* x_141; 
lean_dec(x_1);
x_141 = lean_ctor_get(x_10, 0);
lean_inc(x_141);
lean_dec(x_10);
if (lean_obj_tag(x_141) == 1)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_167 = lean_st_ref_get(x_8, x_9);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_st_ref_get(x_2, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_array_get_size(x_172);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_nat_dec_lt(x_174, x_173);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_173);
lean_dec(x_172);
x_176 = 0;
x_143 = x_176;
x_144 = x_171;
goto block_166;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_le(x_173, x_173);
if (x_177 == 0)
{
uint8_t x_178; 
lean_dec(x_173);
lean_dec(x_172);
x_178 = 0;
x_143 = x_178;
x_144 = x_171;
goto block_166;
}
else
{
size_t x_179; size_t x_180; uint8_t x_181; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_181 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(x_142, x_172, x_179, x_180);
lean_dec(x_172);
x_143 = x_181;
x_144 = x_171;
goto block_166;
}
}
block_166:
{
if (x_143 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_141);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_alreadyVisited(x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_144);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_ToDepElimPattern_markAsVisited(x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_150);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_151, 0);
lean_dec(x_153);
x_154 = l_Lean_Expr_fvarId_x21(x_141);
lean_dec(x_141);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_151, 0, x_155);
return x_151;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_dec(x_151);
x_157 = l_Lean_Expr_fvarId_x21(x_141);
lean_dec(x_141);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
}
else
{
uint8_t x_160; 
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_147);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_147, 0);
lean_dec(x_161);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_141);
lean_ctor_set(x_147, 0, x_162);
return x_147;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
lean_dec(x_147);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_141);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_141);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_9);
return x_183;
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_ToDepElimPattern_main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_ToDepElimPattern_main___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_LocalDecl_fvarId(x_6);
lean_dec(x_6);
x_8 = lean_local_ctx_erase(x_4, x_7);
x_9 = 1;
x_10 = x_2 + x_9;
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_LocalContext_addDecl(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
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
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = x_2;
x_15 = lean_box_usize(x_12);
x_16 = l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1;
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed), 11, 3);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_14);
x_18 = l_Lean_NameSet_empty;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_st_ref_get(x_9, x_10);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_mk_ref(x_19, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = x_17;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_23);
x_26 = lean_apply_8(x_25, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_9, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_23, x_30);
lean_dec(x_23);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = x_34;
x_38 = lean_box_usize(x_36);
x_39 = l_Lean_Elab_Term_withDepElimPatterns___rarg___boxed__const__1;
x_40 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed), 10, 3);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
lean_closure_set(x_40, 2, x_37);
x_41 = x_40;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = lean_apply_7(x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_6, 1);
x_47 = lean_array_get_size(x_43);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_47);
x_50 = lean_apply_9(x_3, x_43, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_47, x_47);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = lean_apply_9(x_3, x_43, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_52;
}
else
{
size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_43, x_13, x_53, x_46);
x_55 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_43, x_13, x_53, x_54);
lean_ctor_set(x_6, 1, x_55);
x_56 = lean_apply_9(x_3, x_43, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_6, 0);
x_58 = lean_ctor_get(x_6, 1);
x_59 = lean_ctor_get(x_6, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_6);
x_60 = lean_array_get_size(x_43);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_apply_9(x_3, x_43, x_27, x_4, x_5, x_63, x_7, x_8, x_9, x_44);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_60, x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_59);
x_67 = lean_apply_9(x_3, x_43, x_27, x_4, x_5, x_66, x_7, x_8, x_9, x_44);
return x_67;
}
else
{
size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_43, x_13, x_68, x_58);
x_70 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_43, x_13, x_68, x_69);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_59);
x_72 = lean_apply_9(x_3, x_43, x_27, x_4, x_5, x_71, x_7, x_8, x_9, x_44);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_42);
if (x_73 == 0)
{
return x_42;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_42, 0);
x_75 = lean_ctor_get(x_42, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_42);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_26);
if (x_77 == 0)
{
return x_26;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_26, 0);
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_26);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
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
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_12);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_PersistentArray_push___rarg(x_21, x_23);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_st_ref_set(x_8, x_15, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_inc(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_33, x_35);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
lean_ctor_set(x_15, 3, x_37);
x_38 = lean_st_ref_set(x_8, x_15, x_17);
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
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_48 = x_16;
} else {
 lean_dec_ref(x_16);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_12);
lean_inc(x_10);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_47, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_46);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_st_ref_set(x_8, x_53, x_17);
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
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_elabMatchAltView___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
lean_object* l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__3(lean_object* x_1) {
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
lean_object* l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__4(lean_object* x_1) {
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
x_6 = l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__3(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__4(x_5);
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
x_11 = l_Std_fmt___at_Lean_Elab_Term_elabMatchAltView___spec__3(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__4(x_10);
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
x_35 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
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
x_20 = l_Lean_addTrace___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
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
lean_object* x_30; 
lean_inc(x_7);
x_30 = l_Lean_Meta_mkLambdaFVars(x_28, x_17, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_3, x_2, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_33;
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_28);
x_38 = l_Lean_mkSimpleThunk(x_17);
x_39 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_3, x_2, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
x_44 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_25 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__4(x_24);
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
x_31 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
x_55 = lean_ctor_get(x_7, 2);
x_56 = lean_ctor_get(x_7, 3);
x_57 = lean_ctor_get(x_7, 4);
x_58 = lean_ctor_get(x_7, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_59 = l_Lean_replaceRef(x_10, x_56);
lean_dec(x_56);
lean_dec(x_10);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_58);
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
x_92 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_91, x_3, x_4, x_5, x_6, x_60, x_8, x_90);
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
lean_inc(x_64);
x_71 = lean_array_to_list(lean_box(0), x_64);
x_72 = l_List_map___at_Lean_Elab_Term_elabMatchAltView___spec__4(x_71);
x_73 = l_Lean_MessageData_ofList(x_72);
lean_dec(x_72);
x_74 = l_Lean_Elab_Term_elabMatchAltView___closed__2;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_KernelException_toMessageData___closed__15;
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
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_elabMatchAltView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_11811____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ignoreUnusedAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if true, do not generate error if an alternative is not used");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Lean_Elab_Term_ignoreUnusedAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_ignoreUnusedAlts___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_ignoreUnusedAlts(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object* x_1) {
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
x_9 = l_Array_instToStringArray___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_5);
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
x_19 = l_Array_instToStringArray___rarg___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_instInhabitedParserDescr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(x_5);
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
x_11 = l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_reportMatcherResultErrors___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_Elab_Term_ignoreUnusedAlts(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_List_isEmpty___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_12);
x_15 = l_List_map___at_Lean_Elab_Term_reportMatcherResultErrors___spec__2(x_14);
x_16 = l_Lean_MessageData_ofList(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__15;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_reportMatcherResultErrors___spec__3(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
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
x_14 = l_Lean_KernelException_toMessageData___closed__15;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_reportMatcherResultErrors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_reportMatcherResultErrors___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid match-expression, type of pattern variable '");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' contains metavariables");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_Lean_LocalDecl_hasExprMVar(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = l_Lean_LocalDecl_toExpr(x_12);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_LocalDecl_type(x_12);
x_24 = l_Lean_indentExpr(x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_KernelException_toMessageData___closed__15;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___boxed), 8, 1);
lean_closure_set(x_28, 0, x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_29 = l_Lean_Meta_withExistingLocalDecls___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__3___rarg(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_2 = x_13;
x_3 = x_31;
x_10 = x_30;
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
}
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_9, x_1, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid match-expression, pattern contains metavariables");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_indentExpr(x_1);
x_10 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_KernelException_toMessageData___closed__15;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___boxed), 8, 0);
return x_1;
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
x_17 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___boxed), 8, 1);
lean_closure_set(x_17, 0, x_12);
x_18 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_26 = l_Lean_replaceRef(x_18, x_23);
lean_dec(x_23);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
x_28 = lean_box(0);
lean_inc(x_7);
lean_inc(x_27);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_19);
x_29 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(x_19, x_19, x_28, x_2, x_3, x_4, x_5, x_27, x_7, x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_16, 2);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(x_19, x_31, x_28, x_2, x_3, x_4, x_5, x_27, x_7, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_16);
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
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_16);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_free_object(x_1);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
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
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_27);
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
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
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
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
return x_15;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_59 = l_Lean_Meta_Match_instantiateAltLHSMVars(x_58, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_6, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_6, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_6, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_6, 5);
lean_inc(x_69);
x_70 = l_Lean_replaceRef(x_62, x_67);
lean_dec(x_67);
lean_dec(x_62);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
x_72 = lean_box(0);
lean_inc(x_7);
lean_inc(x_71);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_63);
x_73 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(x_63, x_63, x_72, x_2, x_3, x_4, x_5, x_71, x_7, x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_60, 2);
lean_inc(x_75);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_76 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5(x_63, x_75, x_72, x_2, x_3, x_4, x_5, x_71, x_7, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_60);
lean_ctor_set(x_82, 1, x_79);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_60);
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
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_76, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_90 = x_76;
} else {
 lean_dec_ref(x_76);
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
lean_dec(x_71);
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_ctor_get(x_73, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_73, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_94 = x_73;
} else {
 lean_dec_ref(x_73);
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
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_59, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_59, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_98 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_20 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
x_22 = l_Lean_throwError___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__8(x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9);
lean_dec(x_21);
return x_22;
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
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
x_151 = lean_st_ref_get(x_10, x_15);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_9, 3);
lean_inc(x_155);
x_156 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_153);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_9, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_9, 2);
lean_inc(x_160);
x_161 = lean_st_ref_get(x_10, x_158);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_154);
x_165 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_165, 0, x_154);
x_166 = x_165;
x_167 = lean_environment_main_module(x_154);
x_168 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_157);
lean_ctor_set(x_168, 3, x_159);
lean_ctor_set(x_168, 4, x_160);
lean_ctor_set(x_168, 5, x_155);
x_169 = l_Lean_Elab_Term_expandMacrosInPatterns(x_18, x_168, x_164);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_st_ref_take(x_10, x_163);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = !lean_is_exclusive(x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_173, 1);
lean_dec(x_176);
lean_ctor_set(x_173, 1, x_171);
x_177 = lean_st_ref_set(x_10, x_173, x_174);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_19 = x_170;
x_20 = x_178;
goto block_150;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_ctor_get(x_173, 2);
x_181 = lean_ctor_get(x_173, 3);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_173);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_171);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
x_183 = lean_st_ref_set(x_10, x_182, x_174);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_19 = x_170;
x_20 = x_184;
goto block_150;
}
}
else
{
lean_object* x_185; 
lean_dec(x_17);
lean_dec(x_16);
x_185 = lean_ctor_get(x_169, 0);
lean_inc(x_185);
lean_dec(x_169);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__7(x_186, x_189, x_5, x_6, x_7, x_8, x_9, x_10, x_163);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_186);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
return x_190;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_190);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
else
{
lean_object* x_195; uint8_t x_196; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_195 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__9___rarg(x_163);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
return x_195;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_195);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
block_150:
{
lean_object* x_21; uint8_t x_127; lean_object* x_128; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_st_ref_get(x_10, x_20);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*1);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_dec(x_138);
x_143 = 0;
x_127 = x_143;
x_128 = x_142;
goto block_137;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_dec(x_138);
x_145 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_146 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_145, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unbox(x_147);
lean_dec(x_147);
x_127 = x_149;
x_128 = x_148;
goto block_137;
}
block_126:
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_array_get_size(x_19);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = x_19;
x_26 = lean_box_usize(x_23);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed__const__1;
lean_inc(x_17);
x_28 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__1___boxed), 11, 4);
lean_closure_set(x_28, 0, x_17);
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_25);
x_29 = x_28;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = lean_apply_7(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_get_size(x_31);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
lean_inc(x_31);
x_37 = x_31;
x_38 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__2(x_36, x_24, x_37);
x_39 = x_38;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l_Lean_Meta_instantiateMVars(x_17, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_to_list(lean_box(0), x_31);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_List_mapM___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__6(x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_16);
x_48 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1;
lean_inc(x_5);
x_49 = l_Lean_Elab_Term_mkAuxName(x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_47);
lean_inc(x_41);
x_52 = l_Lean_Meta_Match_mkMatcher(x_50, x_41, x_47, x_45, x_7, x_8, x_9, x_10, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_47);
x_56 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_getNumExplicitCtorParams___spec__2___rarg(x_41, x_55, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_5);
lean_inc(x_53);
x_60 = l_Lean_Elab_Term_reportMatcherResultErrors(x_53, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec(x_53);
x_64 = l_Lean_mkApp(x_63, x_58);
x_65 = l_Lean_mkAppN(x_64, x_16);
lean_dec(x_16);
x_66 = l_Lean_mkAppN(x_65, x_39);
lean_dec(x_39);
x_82 = lean_st_ref_get(x_10, x_61);
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
x_67 = x_87;
x_68 = x_86;
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_90 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_89, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_91);
lean_dec(x_91);
x_67 = x_93;
x_68 = x_92;
goto block_81;
}
block_81:
{
if (x_67 == 0)
{
lean_object* x_69; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_62);
lean_inc(x_66);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_66);
x_71 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__3;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_KernelException_toMessageData___closed__15;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_76 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_75, x_74, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_66);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_66);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_60);
if (x_94 == 0)
{
return x_60;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_60, 0);
x_96 = lean_ctor_get(x_60, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_60);
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
lean_dec(x_53);
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_98 = !lean_is_exclusive(x_57);
if (x_98 == 0)
{
return x_57;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_57, 0);
x_100 = lean_ctor_get(x_57, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_57);
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
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_102 = !lean_is_exclusive(x_52);
if (x_102 == 0)
{
return x_52;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_52, 0);
x_104 = lean_ctor_get(x_52, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_52);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_106 = !lean_is_exclusive(x_49);
if (x_106 == 0)
{
return x_49;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_49, 0);
x_108 = lean_ctor_get(x_49, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_49);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_44);
if (x_110 == 0)
{
return x_44;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_44, 0);
x_112 = lean_ctor_get(x_44, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_44);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_114 = !lean_is_exclusive(x_40);
if (x_114 == 0)
{
return x_40;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_40, 0);
x_116 = lean_ctor_get(x_40, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_40);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_118 = !lean_is_exclusive(x_33);
if (x_118 == 0)
{
return x_33;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_33, 0);
x_120 = lean_ctor_get(x_33, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_33);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_122 = !lean_is_exclusive(x_30);
if (x_122 == 0)
{
return x_30;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_30, 0);
x_124 = lean_ctor_get(x_30, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_30);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
block_137:
{
if (x_127 == 0)
{
x_21 = x_128;
goto block_126;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_inc(x_17);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_17);
x_130 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___closed__5;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_KernelException_toMessageData___closed__15;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
x_135 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_134, x_133, x_5, x_6, x_7, x_8, x_9, x_10, x_128);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_21 = x_136;
goto block_126;
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_200 = !lean_is_exclusive(x_12);
if (x_200 == 0)
{
return x_12;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_12, 0);
x_202 = lean_ctor_get(x_12, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_12);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
lean_object* l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
x_31 = l_myMacro____x40_Init_Notation___hyg_13348____closed__1;
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
x_38 = l_myMacro____x40_Init_Notation___hyg_1202____closed__23;
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_array_push(x_39, x_38);
x_41 = l_myMacro____x40_Init_Notation___hyg_13348____closed__13;
lean_inc(x_6);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_40, x_42);
x_44 = lean_array_push(x_43, x_10);
x_45 = l_myMacro____x40_Init_Notation___hyg_13348____closed__8;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_33, x_46);
x_48 = l_myMacro____x40_Init_Notation___hyg_13348____closed__6;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_34, x_49);
x_51 = l_myMacro____x40_Init_Notation___hyg_13348____closed__15;
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
x_58 = l_myMacro____x40_Init_Notation___hyg_13348____closed__2;
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
x_62 = l_myMacro____x40_Init_Notation___hyg_13348____closed__1;
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
x_69 = l_myMacro____x40_Init_Notation___hyg_1202____closed__23;
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_array_push(x_70, x_69);
x_72 = l_myMacro____x40_Init_Notation___hyg_13348____closed__13;
lean_inc(x_6);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_71, x_73);
x_75 = lean_array_push(x_74, x_10);
x_76 = l_myMacro____x40_Init_Notation___hyg_13348____closed__8;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_64, x_77);
x_79 = l_myMacro____x40_Init_Notation___hyg_13348____closed__6;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_65, x_80);
x_82 = l_myMacro____x40_Init_Notation___hyg_13348____closed__15;
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
x_89 = l_myMacro____x40_Init_Notation___hyg_13348____closed__2;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_33 = lean_ctor_get(x_4, 4);
lean_dec(x_33);
lean_ctor_set(x_4, 4, x_28);
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
x_43 = l_Lean_instInhabitedSourceInfo___closed__1;
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
x_49 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
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
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
x_58 = lean_ctor_get(x_4, 2);
x_59 = lean_ctor_get(x_4, 3);
x_60 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_61 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_62 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_63 = lean_ctor_get(x_4, 5);
lean_inc(x_63);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_64 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_58);
lean_ctor_set(x_64, 3, x_59);
lean_ctor_set(x_64, 4, x_28);
lean_ctor_set(x_64, 5, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 1, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 2, x_62);
x_65 = l_Lean_Elab_Term_getCurrMacroScope(x_64, x_5, x_6, x_7, x_8, x_9, x_31);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
x_72 = l_Lean_addMacroScope(x_69, x_71, x_66);
x_73 = lean_box(0);
x_74 = l_Lean_instInhabitedSourceInfo___closed__1;
x_75 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_73);
x_77 = l_Lean_Syntax_getId(x_76);
x_78 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_76);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_79 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_80 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_79, x_64, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_6);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_box(0);
x_86 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_76, x_3, x_1, x_18, x_74, x_71, x_75, x_73, x_20, x_85, x_64, x_5, x_6, x_7, x_8, x_9, x_70);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_87 = lean_ctor_get(x_25, 0);
x_88 = lean_ctor_get(x_25, 1);
x_89 = lean_ctor_get(x_25, 2);
x_90 = lean_ctor_get(x_25, 3);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_25);
x_91 = lean_nat_add(x_88, x_19);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
x_93 = lean_st_ref_set(x_9, x_92, x_26);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_4, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_4, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_4, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_4, 3);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_100 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_101 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_102 = lean_ctor_get(x_4, 5);
lean_inc(x_102);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_103 = x_4;
} else {
 lean_dec_ref(x_4);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 6, 3);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_97);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_88);
lean_ctor_set(x_104, 5, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*6, x_99);
lean_ctor_set_uint8(x_104, sizeof(void*)*6 + 1, x_100);
lean_ctor_set_uint8(x_104, sizeof(void*)*6 + 2, x_101);
x_105 = l_Lean_Elab_Term_getCurrMacroScope(x_104, x_5, x_6, x_7, x_8, x_9, x_94);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName___closed__2;
x_112 = l_Lean_addMacroScope(x_109, x_111, x_106);
x_113 = lean_box(0);
x_114 = l_Lean_instInhabitedSourceInfo___closed__1;
x_115 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__2;
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set(x_116, 3, x_113);
x_117 = l_Lean_Syntax_getId(x_116);
x_118 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_isAuxDiscrName(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_119 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___closed__5;
x_120 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_119, x_104, x_5, x_6, x_7, x_8, x_9, x_110);
lean_dec(x_6);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_box(0);
x_126 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f_loop___lambda__1(x_17, x_116, x_3, x_1, x_18, x_114, x_111, x_115, x_113, x_20, x_125, x_104, x_5, x_6, x_7, x_8, x_9, x_110);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_22);
lean_dec(x_20);
x_127 = lean_ctor_get(x_21, 1);
lean_inc(x_127);
lean_dec(x_21);
x_128 = lean_array_push(x_3, x_17);
x_2 = x_18;
x_3 = x_128;
x_10 = x_127;
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 == x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_12, x_13);
lean_dec(x_12);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_isLocalIdent_x3f(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_16);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = 1;
x_27 = x_2 + x_26;
x_2 = x_27;
x_10 = x_25;
goto _start;
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
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
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_34 = lean_array_get_size(x_14);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_34);
x_37 = 1;
x_15 = x_37;
x_16 = x_8;
goto block_33;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_34, x_34);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_34);
x_39 = 1;
x_15 = x_39;
x_16 = x_8;
goto block_33;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_34);
lean_dec(x_34);
lean_inc(x_4);
x_42 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(x_14, x_40, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = 1;
x_15 = x_46;
x_16 = x_45;
goto block_33;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = 0;
x_15 = x_48;
x_16 = x_47;
goto block_33;
}
}
}
block_33:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_to_list(lean_box(0), x_14);
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
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
x_28 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_21, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
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
x_74 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_56 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabDiscrsWitMatchType___spec__1___lambda__1___closed__5;
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
x_18 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_2982____spec__3(x_15, x_16, x_17);
x_19 = x_18;
lean_inc(x_1);
x_20 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getMatchAlts(x_1);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux(x_19, x_20, x_22, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_22);
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
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_2 + x_10;
x_2 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
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
lean_object* x_10; lean_object* x_62; uint8_t x_63; 
x_62 = l_myMacro____x40_Init_Notation___hyg_11811____closed__2;
lean_inc(x_1);
x_63 = l_Lean_Syntax_isOfKind(x_1, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_64 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_68 = lean_unsigned_to_nat(2u);
x_69 = l_Lean_Syntax_getArg(x_1, x_68);
x_70 = l_Lean_Syntax_isNone(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_array_get_size(x_67);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_67);
x_74 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_71, x_71);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_67);
x_76 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
return x_76;
}
else
{
size_t x_77; size_t x_78; uint8_t x_79; 
x_77 = 0;
x_78 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_79 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_67, x_77, x_78);
lean_dec(x_67);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_69);
x_80 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_2);
lean_dec(x_1);
x_81 = l_Lean_Elab_Term_elabMatch___closed__3;
x_82 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_69, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_69);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_69);
lean_dec(x_67);
x_87 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_64, 1);
lean_inc(x_88);
lean_dec(x_64);
x_89 = lean_ctor_get(x_65, 0);
lean_inc(x_89);
lean_dec(x_65);
x_90 = !lean_is_exclusive(x_3);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_3, 3);
lean_inc(x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_3, 3, x_93);
x_94 = 1;
x_95 = l_Lean_Elab_Term_elabTerm(x_89, x_2, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_3, 0);
x_97 = lean_ctor_get(x_3, 1);
x_98 = lean_ctor_get(x_3, 2);
x_99 = lean_ctor_get(x_3, 3);
x_100 = lean_ctor_get(x_3, 4);
x_101 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_102 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_103 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_104 = lean_ctor_get(x_3, 5);
lean_inc(x_104);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_3);
lean_inc(x_89);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_89);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_99);
x_107 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_107, 0, x_96);
lean_ctor_set(x_107, 1, x_97);
lean_ctor_set(x_107, 2, x_98);
lean_ctor_set(x_107, 3, x_106);
lean_ctor_set(x_107, 4, x_100);
lean_ctor_set(x_107, 5, x_104);
lean_ctor_set_uint8(x_107, sizeof(void*)*6, x_101);
lean_ctor_set_uint8(x_107, sizeof(void*)*6 + 1, x_102);
lean_ctor_set_uint8(x_107, sizeof(void*)*6 + 2, x_103);
x_108 = 1;
x_109 = l_Lean_Elab_Term_elabTerm(x_89, x_2, x_108, x_107, x_4, x_5, x_6, x_7, x_8, x_88);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_64);
if (x_110 == 0)
{
return x_64;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_64, 0);
x_112 = lean_ctor_get(x_64, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_64);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_unsigned_to_nat(1u);
x_115 = l_Lean_Syntax_getArg(x_1, x_114);
x_116 = l_Lean_nullKind___closed__2;
lean_inc(x_115);
x_117 = l_Lean_Syntax_isOfKind(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
x_118 = lean_box(0);
x_10 = x_118;
goto block_61;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = l_Lean_Syntax_getArgs(x_115);
x_120 = lean_array_get_size(x_119);
lean_dec(x_119);
x_121 = lean_nat_dec_eq(x_120, x_114);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_115);
x_122 = lean_box(0);
x_10 = x_122;
goto block_61;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_unsigned_to_nat(0u);
x_124 = l_Lean_Syntax_getArg(x_115, x_123);
lean_dec(x_115);
x_125 = l_myMacro____x40_Init_Notation___hyg_11811____closed__6;
lean_inc(x_124);
x_126 = l_Lean_Syntax_isOfKind(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_124);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_127 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_131 = lean_unsigned_to_nat(2u);
x_132 = l_Lean_Syntax_getArg(x_1, x_131);
x_133 = l_Lean_Syntax_isNone(x_132);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_array_get_size(x_130);
x_135 = lean_nat_dec_lt(x_123, x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_130);
x_136 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
return x_136;
}
else
{
uint8_t x_137; 
x_137 = lean_nat_dec_le(x_134, x_134);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_130);
x_138 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
return x_138;
}
else
{
size_t x_139; size_t x_140; uint8_t x_141; 
x_139 = 0;
x_140 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_141 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_130, x_139, x_140);
lean_dec(x_130);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_132);
x_142 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_2);
lean_dec(x_1);
x_143 = l_Lean_Elab_Term_elabMatch___closed__3;
x_144 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_132, x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_132);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
}
else
{
lean_object* x_149; 
lean_dec(x_132);
lean_dec(x_130);
x_149 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_127, 1);
lean_inc(x_150);
lean_dec(x_127);
x_151 = lean_ctor_get(x_128, 0);
lean_inc(x_151);
lean_dec(x_128);
x_152 = !lean_is_exclusive(x_3);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_3, 3);
lean_inc(x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_1);
lean_ctor_set(x_154, 1, x_151);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
lean_ctor_set(x_3, 3, x_155);
x_156 = 1;
x_157 = l_Lean_Elab_Term_elabTerm(x_151, x_2, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_150);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; 
x_158 = lean_ctor_get(x_3, 0);
x_159 = lean_ctor_get(x_3, 1);
x_160 = lean_ctor_get(x_3, 2);
x_161 = lean_ctor_get(x_3, 3);
x_162 = lean_ctor_get(x_3, 4);
x_163 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_164 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_165 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_166 = lean_ctor_get(x_3, 5);
lean_inc(x_166);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_3);
lean_inc(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_1);
lean_ctor_set(x_167, 1, x_151);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_161);
x_169 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set(x_169, 2, x_160);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set(x_169, 4, x_162);
lean_ctor_set(x_169, 5, x_166);
lean_ctor_set_uint8(x_169, sizeof(void*)*6, x_163);
lean_ctor_set_uint8(x_169, sizeof(void*)*6 + 1, x_164);
lean_ctor_set_uint8(x_169, sizeof(void*)*6 + 2, x_165);
x_170 = 1;
x_171 = l_Lean_Elab_Term_elabTerm(x_151, x_2, x_170, x_169, x_4, x_5, x_6, x_7, x_8, x_150);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_127);
if (x_172 == 0)
{
return x_127;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_127, 0);
x_174 = lean_ctor_get(x_127, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_127);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; uint8_t x_177; 
x_176 = l_Lean_Syntax_getArg(x_124, x_123);
lean_inc(x_176);
x_177 = l_Lean_Syntax_isOfKind(x_176, x_116);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_176);
lean_dec(x_124);
x_178 = lean_box(0);
x_10 = x_178;
goto block_61;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Lean_Syntax_getArgs(x_176);
lean_dec(x_176);
x_180 = lean_array_get_size(x_179);
lean_dec(x_179);
x_181 = lean_nat_dec_eq(x_180, x_123);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_124);
x_182 = lean_box(0);
x_10 = x_182;
goto block_61;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_417; 
x_183 = l_Lean_Syntax_getArg(x_124, x_114);
lean_dec(x_124);
x_184 = lean_unsigned_to_nat(2u);
x_185 = l_Lean_Syntax_getArg(x_1, x_184);
lean_inc(x_185);
x_417 = l_Lean_Syntax_isOfKind(x_185, x_116);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_box(0);
x_186 = x_418;
goto block_416;
}
else
{
lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_419 = l_Lean_Syntax_getArgs(x_185);
x_420 = lean_array_get_size(x_419);
lean_dec(x_419);
x_421 = lean_nat_dec_eq(x_420, x_123);
lean_dec(x_420);
if (x_421 == 0)
{
lean_object* x_422; 
x_422 = lean_box(0);
x_186 = x_422;
goto block_416;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
lean_dec(x_185);
x_423 = lean_unsigned_to_nat(4u);
x_424 = l_Lean_Syntax_getArg(x_1, x_423);
x_425 = l_myMacro____x40_Init_Notation___hyg_11811____closed__11;
lean_inc(x_424);
x_426 = l_Lean_Syntax_isOfKind(x_424, x_425);
if (x_426 == 0)
{
lean_object* x_427; 
lean_dec(x_424);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_427 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_431 = l_Lean_Syntax_getArg(x_1, x_184);
x_432 = l_Lean_Syntax_isNone(x_431);
if (x_432 == 0)
{
lean_object* x_433; uint8_t x_434; 
x_433 = lean_array_get_size(x_430);
x_434 = lean_nat_dec_lt(x_123, x_433);
if (x_434 == 0)
{
lean_object* x_435; 
lean_dec(x_433);
lean_dec(x_431);
lean_dec(x_430);
x_435 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
return x_435;
}
else
{
uint8_t x_436; 
x_436 = lean_nat_dec_le(x_433, x_433);
if (x_436 == 0)
{
lean_object* x_437; 
lean_dec(x_433);
lean_dec(x_431);
lean_dec(x_430);
x_437 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
return x_437;
}
else
{
size_t x_438; size_t x_439; uint8_t x_440; 
x_438 = 0;
x_439 = lean_usize_of_nat(x_433);
lean_dec(x_433);
x_440 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_430, x_438, x_439);
lean_dec(x_430);
if (x_440 == 0)
{
lean_object* x_441; 
lean_dec(x_431);
x_441 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; uint8_t x_444; 
lean_dec(x_2);
lean_dec(x_1);
x_442 = l_Lean_Elab_Term_elabMatch___closed__3;
x_443 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_431, x_442, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_431);
x_444 = !lean_is_exclusive(x_443);
if (x_444 == 0)
{
return x_443;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_443, 0);
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_443);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
}
else
{
lean_object* x_448; 
lean_dec(x_431);
lean_dec(x_430);
x_448 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_449 = lean_ctor_get(x_427, 1);
lean_inc(x_449);
lean_dec(x_427);
x_450 = lean_ctor_get(x_428, 0);
lean_inc(x_450);
lean_dec(x_428);
x_451 = !lean_is_exclusive(x_3);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_3, 3);
lean_inc(x_450);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_1);
lean_ctor_set(x_453, 1, x_450);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_452);
lean_ctor_set(x_3, 3, x_454);
x_455 = 1;
x_456 = l_Lean_Elab_Term_elabTerm(x_450, x_2, x_455, x_3, x_4, x_5, x_6, x_7, x_8, x_449);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; 
x_457 = lean_ctor_get(x_3, 0);
x_458 = lean_ctor_get(x_3, 1);
x_459 = lean_ctor_get(x_3, 2);
x_460 = lean_ctor_get(x_3, 3);
x_461 = lean_ctor_get(x_3, 4);
x_462 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_463 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_464 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_465 = lean_ctor_get(x_3, 5);
lean_inc(x_465);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_3);
lean_inc(x_450);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_1);
lean_ctor_set(x_466, 1, x_450);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_460);
x_468 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_468, 0, x_457);
lean_ctor_set(x_468, 1, x_458);
lean_ctor_set(x_468, 2, x_459);
lean_ctor_set(x_468, 3, x_467);
lean_ctor_set(x_468, 4, x_461);
lean_ctor_set(x_468, 5, x_465);
lean_ctor_set_uint8(x_468, sizeof(void*)*6, x_462);
lean_ctor_set_uint8(x_468, sizeof(void*)*6 + 1, x_463);
lean_ctor_set_uint8(x_468, sizeof(void*)*6 + 2, x_464);
x_469 = 1;
x_470 = l_Lean_Elab_Term_elabTerm(x_450, x_2, x_469, x_468, x_4, x_5, x_6, x_7, x_8, x_449);
return x_470;
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_471 = !lean_is_exclusive(x_427);
if (x_471 == 0)
{
return x_427;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_427, 0);
x_473 = lean_ctor_get(x_427, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_427);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
else
{
lean_object* x_475; uint8_t x_476; 
x_475 = l_Lean_Syntax_getArg(x_424, x_123);
lean_dec(x_424);
lean_inc(x_475);
x_476 = l_Lean_Syntax_isOfKind(x_475, x_116);
if (x_476 == 0)
{
lean_object* x_477; 
lean_dec(x_475);
lean_dec(x_183);
x_477 = lean_box(0);
x_10 = x_477;
goto block_61;
}
else
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_478 = l_Lean_Syntax_getArgs(x_475);
x_479 = lean_array_get_size(x_478);
lean_dec(x_478);
x_480 = lean_nat_dec_eq(x_479, x_114);
lean_dec(x_479);
if (x_480 == 0)
{
lean_object* x_481; 
lean_dec(x_475);
lean_dec(x_183);
x_481 = lean_box(0);
x_10 = x_481;
goto block_61;
}
else
{
lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_482 = l_Lean_Syntax_getArg(x_475, x_123);
lean_dec(x_475);
x_483 = l_myMacro____x40_Init_Notation___hyg_11811____closed__13;
lean_inc(x_482);
x_484 = l_Lean_Syntax_isOfKind(x_482, x_483);
if (x_484 == 0)
{
lean_object* x_485; 
lean_dec(x_482);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_485 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_489 = l_Lean_Syntax_getArg(x_1, x_184);
x_490 = l_Lean_Syntax_isNone(x_489);
if (x_490 == 0)
{
lean_object* x_491; uint8_t x_492; 
x_491 = lean_array_get_size(x_488);
x_492 = lean_nat_dec_lt(x_123, x_491);
if (x_492 == 0)
{
lean_object* x_493; 
lean_dec(x_491);
lean_dec(x_489);
lean_dec(x_488);
x_493 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_487);
return x_493;
}
else
{
uint8_t x_494; 
x_494 = lean_nat_dec_le(x_491, x_491);
if (x_494 == 0)
{
lean_object* x_495; 
lean_dec(x_491);
lean_dec(x_489);
lean_dec(x_488);
x_495 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_487);
return x_495;
}
else
{
size_t x_496; size_t x_497; uint8_t x_498; 
x_496 = 0;
x_497 = lean_usize_of_nat(x_491);
lean_dec(x_491);
x_498 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_488, x_496, x_497);
lean_dec(x_488);
if (x_498 == 0)
{
lean_object* x_499; 
lean_dec(x_489);
x_499 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_487);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; uint8_t x_502; 
lean_dec(x_2);
lean_dec(x_1);
x_500 = l_Lean_Elab_Term_elabMatch___closed__3;
x_501 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_489, x_500, x_3, x_4, x_5, x_6, x_7, x_8, x_487);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_489);
x_502 = !lean_is_exclusive(x_501);
if (x_502 == 0)
{
return x_501;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_501, 0);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_501);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
}
}
else
{
lean_object* x_506; 
lean_dec(x_489);
lean_dec(x_488);
x_506 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_487);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; uint8_t x_509; 
x_507 = lean_ctor_get(x_485, 1);
lean_inc(x_507);
lean_dec(x_485);
x_508 = lean_ctor_get(x_486, 0);
lean_inc(x_508);
lean_dec(x_486);
x_509 = !lean_is_exclusive(x_3);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; 
x_510 = lean_ctor_get(x_3, 3);
lean_inc(x_508);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_1);
lean_ctor_set(x_511, 1, x_508);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_510);
lean_ctor_set(x_3, 3, x_512);
x_513 = 1;
x_514 = l_Lean_Elab_Term_elabTerm(x_508, x_2, x_513, x_3, x_4, x_5, x_6, x_7, x_8, x_507);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; uint8_t x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; 
x_515 = lean_ctor_get(x_3, 0);
x_516 = lean_ctor_get(x_3, 1);
x_517 = lean_ctor_get(x_3, 2);
x_518 = lean_ctor_get(x_3, 3);
x_519 = lean_ctor_get(x_3, 4);
x_520 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_521 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_522 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_523 = lean_ctor_get(x_3, 5);
lean_inc(x_523);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_3);
lean_inc(x_508);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_1);
lean_ctor_set(x_524, 1, x_508);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_518);
x_526 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_526, 0, x_515);
lean_ctor_set(x_526, 1, x_516);
lean_ctor_set(x_526, 2, x_517);
lean_ctor_set(x_526, 3, x_525);
lean_ctor_set(x_526, 4, x_519);
lean_ctor_set(x_526, 5, x_523);
lean_ctor_set_uint8(x_526, sizeof(void*)*6, x_520);
lean_ctor_set_uint8(x_526, sizeof(void*)*6 + 1, x_521);
lean_ctor_set_uint8(x_526, sizeof(void*)*6 + 2, x_522);
x_527 = 1;
x_528 = l_Lean_Elab_Term_elabTerm(x_508, x_2, x_527, x_526, x_4, x_5, x_6, x_7, x_8, x_507);
return x_528;
}
}
}
else
{
uint8_t x_529; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_529 = !lean_is_exclusive(x_485);
if (x_529 == 0)
{
return x_485;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_485, 0);
x_531 = lean_ctor_get(x_485, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_485);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
lean_object* x_533; uint8_t x_534; 
x_533 = l_Lean_Syntax_getArg(x_482, x_114);
lean_inc(x_533);
x_534 = l_Lean_Syntax_isOfKind(x_533, x_116);
if (x_534 == 0)
{
lean_object* x_535; 
lean_dec(x_533);
lean_dec(x_482);
lean_dec(x_183);
x_535 = lean_box(0);
x_10 = x_535;
goto block_61;
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_536 = l_Lean_Syntax_getArgs(x_533);
x_537 = lean_array_get_size(x_536);
lean_dec(x_536);
x_538 = lean_nat_dec_eq(x_537, x_114);
lean_dec(x_537);
if (x_538 == 0)
{
lean_object* x_539; 
lean_dec(x_533);
lean_dec(x_482);
lean_dec(x_183);
x_539 = lean_box(0);
x_10 = x_539;
goto block_61;
}
else
{
lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_540 = l_Lean_Syntax_getArg(x_533, x_123);
lean_dec(x_533);
x_541 = l_Lean_identKind___closed__2;
lean_inc(x_540);
x_542 = l_Lean_Syntax_isOfKind(x_540, x_541);
if (x_542 == 0)
{
lean_object* x_543; 
lean_dec(x_540);
lean_dec(x_482);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_543 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_547 = l_Lean_Syntax_getArg(x_1, x_184);
x_548 = l_Lean_Syntax_isNone(x_547);
if (x_548 == 0)
{
lean_object* x_549; uint8_t x_550; 
x_549 = lean_array_get_size(x_546);
x_550 = lean_nat_dec_lt(x_123, x_549);
if (x_550 == 0)
{
lean_object* x_551; 
lean_dec(x_549);
lean_dec(x_547);
lean_dec(x_546);
x_551 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_545);
return x_551;
}
else
{
uint8_t x_552; 
x_552 = lean_nat_dec_le(x_549, x_549);
if (x_552 == 0)
{
lean_object* x_553; 
lean_dec(x_549);
lean_dec(x_547);
lean_dec(x_546);
x_553 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_545);
return x_553;
}
else
{
size_t x_554; size_t x_555; uint8_t x_556; 
x_554 = 0;
x_555 = lean_usize_of_nat(x_549);
lean_dec(x_549);
x_556 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_546, x_554, x_555);
lean_dec(x_546);
if (x_556 == 0)
{
lean_object* x_557; 
lean_dec(x_547);
x_557 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_545);
return x_557;
}
else
{
lean_object* x_558; lean_object* x_559; uint8_t x_560; 
lean_dec(x_2);
lean_dec(x_1);
x_558 = l_Lean_Elab_Term_elabMatch___closed__3;
x_559 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_547, x_558, x_3, x_4, x_5, x_6, x_7, x_8, x_545);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_547);
x_560 = !lean_is_exclusive(x_559);
if (x_560 == 0)
{
return x_559;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_559, 0);
x_562 = lean_ctor_get(x_559, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_559);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
}
}
else
{
lean_object* x_564; 
lean_dec(x_547);
lean_dec(x_546);
x_564 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_545);
return x_564;
}
}
else
{
lean_object* x_565; lean_object* x_566; uint8_t x_567; 
x_565 = lean_ctor_get(x_543, 1);
lean_inc(x_565);
lean_dec(x_543);
x_566 = lean_ctor_get(x_544, 0);
lean_inc(x_566);
lean_dec(x_544);
x_567 = !lean_is_exclusive(x_3);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_3, 3);
lean_inc(x_566);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_1);
lean_ctor_set(x_569, 1, x_566);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_568);
lean_ctor_set(x_3, 3, x_570);
x_571 = 1;
x_572 = l_Lean_Elab_Term_elabTerm(x_566, x_2, x_571, x_3, x_4, x_5, x_6, x_7, x_8, x_565);
return x_572;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; uint8_t x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; uint8_t x_585; lean_object* x_586; 
x_573 = lean_ctor_get(x_3, 0);
x_574 = lean_ctor_get(x_3, 1);
x_575 = lean_ctor_get(x_3, 2);
x_576 = lean_ctor_get(x_3, 3);
x_577 = lean_ctor_get(x_3, 4);
x_578 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_579 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_580 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_581 = lean_ctor_get(x_3, 5);
lean_inc(x_581);
lean_inc(x_577);
lean_inc(x_576);
lean_inc(x_575);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_3);
lean_inc(x_566);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_1);
lean_ctor_set(x_582, 1, x_566);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_576);
x_584 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_584, 0, x_573);
lean_ctor_set(x_584, 1, x_574);
lean_ctor_set(x_584, 2, x_575);
lean_ctor_set(x_584, 3, x_583);
lean_ctor_set(x_584, 4, x_577);
lean_ctor_set(x_584, 5, x_581);
lean_ctor_set_uint8(x_584, sizeof(void*)*6, x_578);
lean_ctor_set_uint8(x_584, sizeof(void*)*6 + 1, x_579);
lean_ctor_set_uint8(x_584, sizeof(void*)*6 + 2, x_580);
x_585 = 1;
x_586 = l_Lean_Elab_Term_elabTerm(x_566, x_2, x_585, x_584, x_4, x_5, x_6, x_7, x_8, x_565);
return x_586;
}
}
}
else
{
uint8_t x_587; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_587 = !lean_is_exclusive(x_543);
if (x_587 == 0)
{
return x_543;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_543, 0);
x_589 = lean_ctor_get(x_543, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_543);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
return x_590;
}
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_unsigned_to_nat(3u);
x_592 = l_Lean_Syntax_getArg(x_482, x_591);
lean_dec(x_482);
x_593 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatch(x_1, x_183, x_540, x_592, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_593;
}
}
}
}
}
}
}
}
}
block_416:
{
uint8_t x_187; 
lean_dec(x_186);
lean_inc(x_185);
x_187 = l_Lean_Syntax_isOfKind(x_185, x_116);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_185);
lean_dec(x_183);
x_188 = lean_box(0);
x_10 = x_188;
goto block_61;
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = l_Lean_Syntax_getArgs(x_185);
x_190 = lean_array_get_size(x_189);
lean_dec(x_189);
x_191 = lean_nat_dec_eq(x_190, x_114);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
lean_dec(x_185);
lean_dec(x_183);
x_192 = lean_box(0);
x_10 = x_192;
goto block_61;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = l_Lean_Syntax_getArg(x_185, x_123);
lean_dec(x_185);
x_194 = l_Lean_expandExplicitBindersAux_loop___closed__6;
lean_inc(x_193);
x_195 = l_Lean_Syntax_isOfKind(x_193, x_194);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_193);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_196 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_200 = l_Lean_Syntax_getArg(x_1, x_184);
x_201 = l_Lean_Syntax_isNone(x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_array_get_size(x_199);
x_203 = lean_nat_dec_lt(x_123, x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
x_204 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
return x_204;
}
else
{
uint8_t x_205; 
x_205 = lean_nat_dec_le(x_202, x_202);
if (x_205 == 0)
{
lean_object* x_206; 
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_199);
x_206 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
return x_206;
}
else
{
size_t x_207; size_t x_208; uint8_t x_209; 
x_207 = 0;
x_208 = lean_usize_of_nat(x_202);
lean_dec(x_202);
x_209 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_199, x_207, x_208);
lean_dec(x_199);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_200);
x_210 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_2);
lean_dec(x_1);
x_211 = l_Lean_Elab_Term_elabMatch___closed__3;
x_212 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_200, x_211, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_200);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
return x_212;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_212);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
}
else
{
lean_object* x_217; 
lean_dec(x_200);
lean_dec(x_199);
x_217 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_196, 1);
lean_inc(x_218);
lean_dec(x_196);
x_219 = lean_ctor_get(x_197, 0);
lean_inc(x_219);
lean_dec(x_197);
x_220 = !lean_is_exclusive(x_3);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_3, 3);
lean_inc(x_219);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_1);
lean_ctor_set(x_222, 1, x_219);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
lean_ctor_set(x_3, 3, x_223);
x_224 = 1;
x_225 = l_Lean_Elab_Term_elabTerm(x_219, x_2, x_224, x_3, x_4, x_5, x_6, x_7, x_8, x_218);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; 
x_226 = lean_ctor_get(x_3, 0);
x_227 = lean_ctor_get(x_3, 1);
x_228 = lean_ctor_get(x_3, 2);
x_229 = lean_ctor_get(x_3, 3);
x_230 = lean_ctor_get(x_3, 4);
x_231 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_232 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_233 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_234 = lean_ctor_get(x_3, 5);
lean_inc(x_234);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_3);
lean_inc(x_219);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_1);
lean_ctor_set(x_235, 1, x_219);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_229);
x_237 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_237, 0, x_226);
lean_ctor_set(x_237, 1, x_227);
lean_ctor_set(x_237, 2, x_228);
lean_ctor_set(x_237, 3, x_236);
lean_ctor_set(x_237, 4, x_230);
lean_ctor_set(x_237, 5, x_234);
lean_ctor_set_uint8(x_237, sizeof(void*)*6, x_231);
lean_ctor_set_uint8(x_237, sizeof(void*)*6 + 1, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*6 + 2, x_233);
x_238 = 1;
x_239 = l_Lean_Elab_Term_elabTerm(x_219, x_2, x_238, x_237, x_4, x_5, x_6, x_7, x_8, x_218);
return x_239;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_240 = !lean_is_exclusive(x_196);
if (x_240 == 0)
{
return x_196;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_196, 0);
x_242 = lean_ctor_get(x_196, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_196);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_244 = l_Lean_Syntax_getArg(x_193, x_114);
lean_dec(x_193);
x_245 = lean_unsigned_to_nat(4u);
x_246 = l_Lean_Syntax_getArg(x_1, x_245);
x_247 = l_myMacro____x40_Init_Notation___hyg_11811____closed__11;
lean_inc(x_246);
x_248 = l_Lean_Syntax_isOfKind(x_246, x_247);
if (x_248 == 0)
{
lean_object* x_249; 
lean_dec(x_246);
lean_dec(x_244);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_249 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_253 = l_Lean_Syntax_getArg(x_1, x_184);
x_254 = l_Lean_Syntax_isNone(x_253);
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_array_get_size(x_252);
x_256 = lean_nat_dec_lt(x_123, x_255);
if (x_256 == 0)
{
lean_object* x_257; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_252);
x_257 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_251);
return x_257;
}
else
{
uint8_t x_258; 
x_258 = lean_nat_dec_le(x_255, x_255);
if (x_258 == 0)
{
lean_object* x_259; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_252);
x_259 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_251);
return x_259;
}
else
{
size_t x_260; size_t x_261; uint8_t x_262; 
x_260 = 0;
x_261 = lean_usize_of_nat(x_255);
lean_dec(x_255);
x_262 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_252, x_260, x_261);
lean_dec(x_252);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_253);
x_263 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_251);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; 
lean_dec(x_2);
lean_dec(x_1);
x_264 = l_Lean_Elab_Term_elabMatch___closed__3;
x_265 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_253, x_264, x_3, x_4, x_5, x_6, x_7, x_8, x_251);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_253);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
return x_265;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_265, 0);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_265);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
}
else
{
lean_object* x_270; 
lean_dec(x_253);
lean_dec(x_252);
x_270 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_251);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_ctor_get(x_249, 1);
lean_inc(x_271);
lean_dec(x_249);
x_272 = lean_ctor_get(x_250, 0);
lean_inc(x_272);
lean_dec(x_250);
x_273 = !lean_is_exclusive(x_3);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_3, 3);
lean_inc(x_272);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_1);
lean_ctor_set(x_275, 1, x_272);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
lean_ctor_set(x_3, 3, x_276);
x_277 = 1;
x_278 = l_Lean_Elab_Term_elabTerm(x_272, x_2, x_277, x_3, x_4, x_5, x_6, x_7, x_8, x_271);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; 
x_279 = lean_ctor_get(x_3, 0);
x_280 = lean_ctor_get(x_3, 1);
x_281 = lean_ctor_get(x_3, 2);
x_282 = lean_ctor_get(x_3, 3);
x_283 = lean_ctor_get(x_3, 4);
x_284 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_285 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_286 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_287 = lean_ctor_get(x_3, 5);
lean_inc(x_287);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_3);
lean_inc(x_272);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_1);
lean_ctor_set(x_288, 1, x_272);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_282);
x_290 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_290, 0, x_279);
lean_ctor_set(x_290, 1, x_280);
lean_ctor_set(x_290, 2, x_281);
lean_ctor_set(x_290, 3, x_289);
lean_ctor_set(x_290, 4, x_283);
lean_ctor_set(x_290, 5, x_287);
lean_ctor_set_uint8(x_290, sizeof(void*)*6, x_284);
lean_ctor_set_uint8(x_290, sizeof(void*)*6 + 1, x_285);
lean_ctor_set_uint8(x_290, sizeof(void*)*6 + 2, x_286);
x_291 = 1;
x_292 = l_Lean_Elab_Term_elabTerm(x_272, x_2, x_291, x_290, x_4, x_5, x_6, x_7, x_8, x_271);
return x_292;
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_249);
if (x_293 == 0)
{
return x_249;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_249, 0);
x_295 = lean_ctor_get(x_249, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_249);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; uint8_t x_298; 
x_297 = l_Lean_Syntax_getArg(x_246, x_123);
lean_dec(x_246);
lean_inc(x_297);
x_298 = l_Lean_Syntax_isOfKind(x_297, x_116);
if (x_298 == 0)
{
lean_object* x_299; 
lean_dec(x_297);
lean_dec(x_244);
lean_dec(x_183);
x_299 = lean_box(0);
x_10 = x_299;
goto block_61;
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = l_Lean_Syntax_getArgs(x_297);
x_301 = lean_array_get_size(x_300);
lean_dec(x_300);
x_302 = lean_nat_dec_eq(x_301, x_114);
lean_dec(x_301);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_297);
lean_dec(x_244);
lean_dec(x_183);
x_303 = lean_box(0);
x_10 = x_303;
goto block_61;
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = l_Lean_Syntax_getArg(x_297, x_123);
lean_dec(x_297);
x_305 = l_myMacro____x40_Init_Notation___hyg_11811____closed__13;
lean_inc(x_304);
x_306 = l_Lean_Syntax_isOfKind(x_304, x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_304);
lean_dec(x_244);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_307 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_311 = l_Lean_Syntax_getArg(x_1, x_184);
x_312 = l_Lean_Syntax_isNone(x_311);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_array_get_size(x_310);
x_314 = lean_nat_dec_lt(x_123, x_313);
if (x_314 == 0)
{
lean_object* x_315; 
lean_dec(x_313);
lean_dec(x_311);
lean_dec(x_310);
x_315 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
return x_315;
}
else
{
uint8_t x_316; 
x_316 = lean_nat_dec_le(x_313, x_313);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
lean_dec(x_311);
lean_dec(x_310);
x_317 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
return x_317;
}
else
{
size_t x_318; size_t x_319; uint8_t x_320; 
x_318 = 0;
x_319 = lean_usize_of_nat(x_313);
lean_dec(x_313);
x_320 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_310, x_318, x_319);
lean_dec(x_310);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_311);
x_321 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_2);
lean_dec(x_1);
x_322 = l_Lean_Elab_Term_elabMatch___closed__3;
x_323 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_311, x_322, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_311);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
return x_323;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_323, 0);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_323);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
}
}
else
{
lean_object* x_328; 
lean_dec(x_311);
lean_dec(x_310);
x_328 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_329 = lean_ctor_get(x_307, 1);
lean_inc(x_329);
lean_dec(x_307);
x_330 = lean_ctor_get(x_308, 0);
lean_inc(x_330);
lean_dec(x_308);
x_331 = !lean_is_exclusive(x_3);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_3, 3);
lean_inc(x_330);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_1);
lean_ctor_set(x_333, 1, x_330);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
lean_ctor_set(x_3, 3, x_334);
x_335 = 1;
x_336 = l_Lean_Elab_Term_elabTerm(x_330, x_2, x_335, x_3, x_4, x_5, x_6, x_7, x_8, x_329);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_337 = lean_ctor_get(x_3, 0);
x_338 = lean_ctor_get(x_3, 1);
x_339 = lean_ctor_get(x_3, 2);
x_340 = lean_ctor_get(x_3, 3);
x_341 = lean_ctor_get(x_3, 4);
x_342 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_343 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_344 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_345 = lean_ctor_get(x_3, 5);
lean_inc(x_345);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_3);
lean_inc(x_330);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_1);
lean_ctor_set(x_346, 1, x_330);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_340);
x_348 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_348, 0, x_337);
lean_ctor_set(x_348, 1, x_338);
lean_ctor_set(x_348, 2, x_339);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set(x_348, 4, x_341);
lean_ctor_set(x_348, 5, x_345);
lean_ctor_set_uint8(x_348, sizeof(void*)*6, x_342);
lean_ctor_set_uint8(x_348, sizeof(void*)*6 + 1, x_343);
lean_ctor_set_uint8(x_348, sizeof(void*)*6 + 2, x_344);
x_349 = 1;
x_350 = l_Lean_Elab_Term_elabTerm(x_330, x_2, x_349, x_348, x_4, x_5, x_6, x_7, x_8, x_329);
return x_350;
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_307);
if (x_351 == 0)
{
return x_307;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_307, 0);
x_353 = lean_ctor_get(x_307, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_307);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
lean_object* x_355; uint8_t x_356; 
x_355 = l_Lean_Syntax_getArg(x_304, x_114);
lean_inc(x_355);
x_356 = l_Lean_Syntax_isOfKind(x_355, x_116);
if (x_356 == 0)
{
lean_object* x_357; 
lean_dec(x_355);
lean_dec(x_304);
lean_dec(x_244);
lean_dec(x_183);
x_357 = lean_box(0);
x_10 = x_357;
goto block_61;
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_358 = l_Lean_Syntax_getArgs(x_355);
x_359 = lean_array_get_size(x_358);
lean_dec(x_358);
x_360 = lean_nat_dec_eq(x_359, x_114);
lean_dec(x_359);
if (x_360 == 0)
{
lean_object* x_361; 
lean_dec(x_355);
lean_dec(x_304);
lean_dec(x_244);
lean_dec(x_183);
x_361 = lean_box(0);
x_10 = x_361;
goto block_61;
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_362 = l_Lean_Syntax_getArg(x_355, x_123);
lean_dec(x_355);
x_363 = l_Lean_identKind___closed__2;
lean_inc(x_362);
x_364 = l_Lean_Syntax_isOfKind(x_362, x_363);
if (x_364 == 0)
{
lean_object* x_365; 
lean_dec(x_362);
lean_dec(x_304);
lean_dec(x_244);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_365 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandNonAtomicDiscrs_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_369 = l_Lean_Syntax_getArg(x_1, x_184);
x_370 = l_Lean_Syntax_isNone(x_369);
if (x_370 == 0)
{
lean_object* x_371; uint8_t x_372; 
x_371 = lean_array_get_size(x_368);
x_372 = lean_nat_dec_lt(x_123, x_371);
if (x_372 == 0)
{
lean_object* x_373; 
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_368);
x_373 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
return x_373;
}
else
{
uint8_t x_374; 
x_374 = lean_nat_dec_le(x_371, x_371);
if (x_374 == 0)
{
lean_object* x_375; 
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_368);
x_375 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
return x_375;
}
else
{
size_t x_376; size_t x_377; uint8_t x_378; 
x_376 = 0;
x_377 = lean_usize_of_nat(x_371);
lean_dec(x_371);
x_378 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_368, x_376, x_377);
lean_dec(x_368);
if (x_378 == 0)
{
lean_object* x_379; 
lean_dec(x_369);
x_379 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; 
lean_dec(x_2);
lean_dec(x_1);
x_380 = l_Lean_Elab_Term_elabMatch___closed__3;
x_381 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_369, x_380, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_369);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
return x_381;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_ctor_get(x_381, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_381);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
}
}
else
{
lean_object* x_386; 
lean_dec(x_369);
lean_dec(x_368);
x_386 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_387 = lean_ctor_get(x_365, 1);
lean_inc(x_387);
lean_dec(x_365);
x_388 = lean_ctor_get(x_366, 0);
lean_inc(x_388);
lean_dec(x_366);
x_389 = !lean_is_exclusive(x_3);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_390 = lean_ctor_get(x_3, 3);
lean_inc(x_388);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_1);
lean_ctor_set(x_391, 1, x_388);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
lean_ctor_set(x_3, 3, x_392);
x_393 = 1;
x_394 = l_Lean_Elab_Term_elabTerm(x_388, x_2, x_393, x_3, x_4, x_5, x_6, x_7, x_8, x_387);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_3, 0);
x_396 = lean_ctor_get(x_3, 1);
x_397 = lean_ctor_get(x_3, 2);
x_398 = lean_ctor_get(x_3, 3);
x_399 = lean_ctor_get(x_3, 4);
x_400 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_401 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_402 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_403 = lean_ctor_get(x_3, 5);
lean_inc(x_403);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_3);
lean_inc(x_388);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_1);
lean_ctor_set(x_404, 1, x_388);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_398);
x_406 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_406, 0, x_395);
lean_ctor_set(x_406, 1, x_396);
lean_ctor_set(x_406, 2, x_397);
lean_ctor_set(x_406, 3, x_405);
lean_ctor_set(x_406, 4, x_399);
lean_ctor_set(x_406, 5, x_403);
lean_ctor_set_uint8(x_406, sizeof(void*)*6, x_400);
lean_ctor_set_uint8(x_406, sizeof(void*)*6 + 1, x_401);
lean_ctor_set_uint8(x_406, sizeof(void*)*6 + 2, x_402);
x_407 = 1;
x_408 = l_Lean_Elab_Term_elabTerm(x_388, x_2, x_407, x_406, x_4, x_5, x_6, x_7, x_8, x_387);
return x_408;
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_409 = !lean_is_exclusive(x_365);
if (x_409 == 0)
{
return x_365;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_365, 0);
x_411 = lean_ctor_get(x_365, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_365);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_unsigned_to_nat(3u);
x_414 = l_Lean_Syntax_getArg(x_304, x_413);
lean_dec(x_304);
x_415 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_expandSimpleMatchWithType(x_1, x_183, x_362, x_244, x_414, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_415;
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
block_61:
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_getDiscrs(x_1);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_get_size(x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
x_21 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_14, x_24, x_25);
lean_dec(x_14);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_16);
x_27 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_Elab_Term_elabMatch___closed__3;
x_29 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_16, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_16);
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
}
}
else
{
lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_14);
x_34 = l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_3, 3);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_3, 3, x_40);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTerm(x_36, x_2, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get(x_3, 3);
x_47 = lean_ctor_get(x_3, 4);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_51 = lean_ctor_get(x_3, 5);
lean_inc(x_51);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
lean_inc(x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_36);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_54 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*6 + 1, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*6 + 2, x_50);
x_55 = 1;
x_56 = l_Lean_Elab_Term_elabTerm(x_36, x_2, x_55, x_54, x_4, x_5, x_6, x_7, x_8, x_35);
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
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_11, 0);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_11);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_elabMatch___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
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
x_3 = l_myMacro____x40_Init_Notation___hyg_11811____closed__2;
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
x_18 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addDiscr___closed__1;
x_19 = lean_array_push(x_18, x_14);
x_20 = l_myMacro____x40_Init_Notation___hyg_11811____closed__6;
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
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1___boxed__const__1);
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
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538____closed__2);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_1538_(lean_io_mk_world());
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
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__1);
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_throwAmbiguous___rarg___closed__2);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__3);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__4);
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
l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_CollectPatternVars_CtorApp_processExplicitArg___closed__3);
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
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__3);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__4 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__4);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__5 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812____closed__5);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_5812_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___lambda__1___closed__2);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__1 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__2 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__3);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__4 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__4();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__4___closed__4);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___lambda__2___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___spec__5___closed__1);
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
l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed__const__1 = _init_l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Match_0__Lean_Elab_Term_elabMatchAux___boxed__const__1);
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
