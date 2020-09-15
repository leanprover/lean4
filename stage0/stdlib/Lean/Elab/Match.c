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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__8;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg___closed__3;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_37__withElaboratedLHS___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__11;
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__6;
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_23__processCtorAppAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_12__addAssignmentInfo___closed__4;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__19;
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Elab_Match_28__collect___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__12;
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_5__mkUserNameFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__14;
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__5;
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_46__mkNewAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
lean_object* l___private_Lean_Elab_Match_22__processImplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__1;
lean_object* l___private_Lean_Elab_Match_17__finalize___closed__3;
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__2;
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
extern lean_object* l_Lean_identKind___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__18;
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__15;
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__isDone___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16;
extern lean_object* l_Lean_Name_toExprAux___main___closed__1;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_17__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
lean_object* l___private_Lean_Elab_Match_24__processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__3;
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__5;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__11;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__7;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Lean_Elab_Match_46__mkNewAlts(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_46__mkNewAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
extern lean_object* l_Lean_Name_toExprAux___main___closed__2;
lean_object* l___private_Lean_Elab_Match_23__processCtorAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__14;
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__4;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1___boxed(lean_object**);
extern lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__processImplicitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_42__mkOptType(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1;
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_37__withElaboratedLHS___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13;
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern(lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__pushNewArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Match_16__isDone(lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__quotedNameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__3;
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1;
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_48__regTraceClasses(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_28__collect___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_29__collectPatternVars___closed__1;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9;
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern(lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_46__mkNewAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_29__collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_17__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__10;
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_17__finalize___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_23__processCtorAppAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkFreshUserName___closed__2;
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__2;
extern lean_object* l_Lean_strLitKind;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__19;
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__4;
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExpr___closed__1;
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
lean_object* l___private_Lean_Elab_Match_39__waitExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_17__finalize___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_27__quotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__1;
extern lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__8;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_23__processCtorAppAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6;
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__2;
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__2;
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_27__quotedNameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__6;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2;
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Elab_expandMacros___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalDecl_Inhabited;
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__elabDiscrsWitMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_41__mkMatchType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___closed__3;
lean_object* l___private_Lean_Elab_Match_25__processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__12;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
lean_object* l___private_Lean_Elab_Match_46__mkNewAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__2;
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__14;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15;
lean_object* l___private_Lean_Elab_Match_36__mkLocalDeclFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__3;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
lean_object* l___private_Lean_Elab_Match_33__alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__5;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__18;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__12;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__11;
lean_object* l___private_Lean_Elab_Match_36__mkLocalDeclFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__26;
lean_object* l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___lambda__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2;
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__1;
lean_object* l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_45__mkNewAlt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___main___closed__1;
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6;
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1;
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__3;
uint8_t l___private_Lean_Elab_Match_18__isNextArgAccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8;
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__6;
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main(lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__4;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17;
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3;
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_40__elabMatchCore___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__5;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__7;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__7;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_40__elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__quotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__2;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__getNextParam(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__7;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__5;
lean_object* l___private_Lean_Elab_Match_31__withPatternVars(lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1;
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__1;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_toString___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__1(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4;
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_39__waitExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__3;
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited;
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__9;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__2;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_28__collect___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1;
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__4;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
lean_object* l___private_Lean_Elab_Match_40__elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__4;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__10;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__2;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__3;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_Match_20__pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___closed__1;
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20;
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__8;
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__9;
lean_object* l_Lean_Elab_Term_mkMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__pushNewArg___closed__1;
lean_object* l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_28__collect___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__5;
lean_object* l___private_Lean_Elab_Match_33__alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg___closed__4;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__7;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__8;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
extern lean_object* l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_object* l___private_Lean_Elab_Match_18__isNextArgAccessible___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2;
extern lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__11;
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l___private_Lean_Elab_Match_4__elabDiscrsWitMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__3;
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg___closed__2;
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Match_5__mkUserNameFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__13;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__processVar___closed__6;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__3;
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9;
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___closed__1;
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__6;
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__2(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_46__mkNewAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_45__mkNewAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors___closed__1;
lean_object* l___private_Lean_Elab_Match_28__collect___main___closed__13;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
extern lean_object* l_Lean_matchPatternAttr;
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_object*);
lean_object* l_Lean_mkThunk(lean_object*);
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4;
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Array_empty___closed__1;
x_8 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_6, x_5, x_3, x_7);
lean_dec(x_5);
x_9 = l_Lean_Syntax_getArg(x_2, x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
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
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_array_push(x_20, x_19);
x_22 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_array_push(x_23, x_2);
x_25 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_17, x_26);
x_28 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_31 = lean_array_push(x_30, x_29);
x_32 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_array_push(x_33, x_4);
x_35 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
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
x_53 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
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
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
x_56 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_46);
lean_ctor_set(x_56, 4, x_47);
lean_ctor_set(x_56, 5, x_48);
lean_ctor_set(x_56, 6, x_55);
lean_ctor_set(x_56, 7, x_50);
lean_ctor_set_uint8(x_56, sizeof(void*)*8, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 1, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 2, x_53);
x_57 = 1;
x_58 = l_Lean_Elab_Term_elabTerm(x_36, x_5, x_57, x_56, x_7, x_8, x_9, x_10, x_11, x_16);
return x_58;
}
}
}
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_20 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_21 = lean_array_push(x_19, x_20);
x_22 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__26;
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
x_30 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_array_push(x_31, x_2);
x_33 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_18, x_34);
x_36 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_39 = lean_array_push(x_38, x_37);
x_40 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_array_push(x_41, x_5);
x_43 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
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
x_61 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 2);
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
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_44);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
x_64 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_54);
lean_ctor_set(x_64, 4, x_55);
lean_ctor_set(x_64, 5, x_56);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_64, 7, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*8, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*8 + 1, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*8 + 2, x_61);
x_65 = 1;
x_66 = l_Lean_Elab_Term_elabTerm(x_44, x_6, x_65, x_64, x_8, x_9, x_10, x_11, x_12, x_17);
return x_66;
}
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_formatStxAux___main(x_6, x_7, x_8, x_4);
x_10 = lean_box(0);
x_11 = l_Lean_Format_pretty(x_9, x_10);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2(x_1, x_5);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; 
x_16 = l_String_splitAux___main___closed__1;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = 0;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_formatStxAux___main(x_19, x_20, x_21, x_17);
x_23 = lean_box(0);
x_24 = l_Lean_Format_pretty(x_22, x_23);
x_25 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2(x_20, x_18);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
}
}
lean_object* l_List_toString___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid result type provided to match-expression");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid type provided to match-expression, function type with arity #");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discr #");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
lean_ctor_set_uint8(x_15, 0, x_19);
lean_ctor_set_uint8(x_15, 1, x_19);
lean_ctor_set_uint8(x_15, 2, x_19);
lean_ctor_set_uint8(x_15, 3, x_19);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_21 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_4, x_2, x_6, x_7, x_20, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_5);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_indentExpr(x_4);
x_26 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_MessageData_ofList___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__12;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_2);
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_21, 0);
lean_dec(x_40);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
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
lean_dec(x_4);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get_uint8(x_15, 4);
x_48 = lean_ctor_get_uint8(x_15, 5);
x_49 = lean_ctor_get_uint8(x_15, 6);
x_50 = lean_ctor_get_uint8(x_15, 7);
lean_dec(x_15);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, 2, x_51);
lean_ctor_set_uint8(x_52, 3, x_51);
lean_ctor_set_uint8(x_52, 4, x_47);
lean_ctor_set_uint8(x_52, 5, x_48);
lean_ctor_set_uint8(x_52, 6, x_49);
lean_ctor_set_uint8(x_52, 7, x_50);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_16);
lean_ctor_set(x_53, 2, x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_54 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_4, x_2, x_6, x_7, x_53, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_5);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_indentExpr(x_4);
x_59 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3;
x_60 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_MessageData_ofList___closed__3;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId___closed__12;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_indentExpr(x_2);
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_66, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_73 = x_54;
} else {
 lean_dec_ref(x_54);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_75 = lean_ctor_get(x_54, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_54, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_77 = x_54;
} else {
 lean_dec_ref(x_54);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_array_fget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_80 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 7)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 2);
lean_inc(x_97);
lean_dec(x_81);
lean_inc(x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_ctor_get(x_8, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_8, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_8, 2);
lean_inc(x_101);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_103 = 1;
lean_ctor_set_uint8(x_99, 0, x_103);
lean_ctor_set_uint8(x_99, 1, x_103);
lean_ctor_set_uint8(x_99, 2, x_103);
lean_ctor_set_uint8(x_99, 3, x_103);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_105 = l_Lean_Elab_Term_elabTermEnsuringType(x_79, x_98, x_103, x_6, x_7, x_104, x_9, x_10, x_11, x_82);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_10, 0);
lean_inc(x_108);
x_109 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_110 = l_Lean_checkTraceOption(x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_96);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_add(x_3, x_111);
lean_dec(x_3);
x_113 = lean_expr_instantiate1(x_97, x_106);
lean_dec(x_97);
x_114 = lean_array_push(x_5, x_106);
x_3 = x_112;
x_4 = x_113;
x_5 = x_114;
x_12 = x_107;
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_inc(x_3);
x_116 = l_Nat_repr(x_3);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l___private_Lean_Meta_ExprDefEq_12__addAssignmentInfo___closed__4;
x_122 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_106);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_106);
x_124 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_126 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_96);
x_128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_109, x_128, x_6, x_7, x_8, x_9, x_10, x_11, x_107);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_3, x_131);
lean_dec(x_3);
x_133 = lean_expr_instantiate1(x_97, x_106);
lean_dec(x_97);
x_134 = lean_array_push(x_5, x_106);
x_3 = x_132;
x_4 = x_133;
x_5 = x_134;
x_12 = x_130;
goto _start;
}
}
else
{
uint8_t x_136; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_105);
if (x_136 == 0)
{
return x_105;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_105, 0);
x_138 = lean_ctor_get(x_105, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_105);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get_uint8(x_99, 4);
x_141 = lean_ctor_get_uint8(x_99, 5);
x_142 = lean_ctor_get_uint8(x_99, 6);
x_143 = lean_ctor_get_uint8(x_99, 7);
lean_dec(x_99);
x_144 = 1;
x_145 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_145, 0, x_144);
lean_ctor_set_uint8(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, 2, x_144);
lean_ctor_set_uint8(x_145, 3, x_144);
lean_ctor_set_uint8(x_145, 4, x_140);
lean_ctor_set_uint8(x_145, 5, x_141);
lean_ctor_set_uint8(x_145, 6, x_142);
lean_ctor_set_uint8(x_145, 7, x_143);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_100);
lean_ctor_set(x_146, 2, x_101);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_147 = l_Lean_Elab_Term_elabTermEnsuringType(x_79, x_98, x_144, x_6, x_7, x_146, x_9, x_10, x_11, x_82);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_10, 0);
lean_inc(x_150);
x_151 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_152 = l_Lean_checkTraceOption(x_150, x_151);
lean_dec(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_96);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_add(x_3, x_153);
lean_dec(x_3);
x_155 = lean_expr_instantiate1(x_97, x_148);
lean_dec(x_97);
x_156 = lean_array_push(x_5, x_148);
x_3 = x_154;
x_4 = x_155;
x_5 = x_156;
x_12 = x_149;
goto _start;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_inc(x_3);
x_158 = l_Nat_repr(x_3);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13;
x_162 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l___private_Lean_Meta_ExprDefEq_12__addAssignmentInfo___closed__4;
x_164 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_148);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_148);
x_166 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_168 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_169, 0, x_96);
x_170 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_151, x_170, x_6, x_7, x_8, x_9, x_10, x_11, x_149);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_add(x_3, x_173);
lean_dec(x_3);
x_175 = lean_expr_instantiate1(x_97, x_148);
lean_dec(x_97);
x_176 = lean_array_push(x_5, x_148);
x_3 = x_174;
x_4 = x_175;
x_5 = x_176;
x_12 = x_172;
goto _start;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_147, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_147, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_180 = x_147;
} else {
 lean_dec_ref(x_147);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
else
{
lean_object* x_182; 
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_box(0);
x_83 = x_182;
goto block_95;
}
block_95:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_83);
x_84 = l_Array_toList___rarg(x_1);
x_85 = l_List_toString___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__1(x_84);
x_86 = l_Array_HasRepr___rarg___closed__1;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__6;
x_91 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__9;
x_93 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_93, x_6, x_7, x_8, x_9, x_10, x_11, x_82);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_94;
}
}
else
{
uint8_t x_183; 
lean_dec(x_79);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_183 = !lean_is_exclusive(x_80);
if (x_183 == 0)
{
return x_80;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_80, 0);
x_185 = lean_ctor_get(x_80, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_80);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_4__elabDiscrsWitMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main(x_1, x_3, x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_4__elabDiscrsWitMatchType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_4__elabDiscrsWitMatchType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_7, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_1);
x_22 = lean_local_ctx_find(x_21, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_4, x_5, x_6, x_7, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = l_Lean_TraceState_Inhabited___closed__1;
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_st_ref_set(x_7, x_40, x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_1);
x_44 = lean_local_ctx_find(x_43, x_1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_4, x_5, x_6, x_7, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_4);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_53 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
lean_dec(x_4);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_5__mkUserNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_22 = l_Lean_Elab_Term_mkFreshUserName(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_22;
}
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_5__mkUserNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_5__mkUserNameFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = lean_box(0);
x_19 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Elab_Term_elabTerm(x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
}
}
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = l_Lean_Expr_toHeadIndex___main(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_12);
x_14 = lean_st_ref_get(x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_9, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_9, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_st_mk_ref(x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_11, x_13, x_1, x_12, x_28, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_28, x_32);
lean_dec(x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_28);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = l_Lean_TraceState_Inhabited___closed__1;
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_st_ref_set(x_9, x_50, x_20);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_st_mk_ref(x_53, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_57 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_11, x_13, x_1, x_12, x_55, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_55, x_59);
lean_dec(x_55);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_55);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_dec(x_57);
x_68 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = lean_array_fget(x_2, x_16);
lean_inc(x_6);
x_18 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_19);
x_21 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_6);
x_24 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_19);
x_28 = l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__2(x_5, x_19, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_6);
x_31 = l___private_Lean_Elab_Match_5__mkUserNameFor(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
x_35 = l_Lean_mkForall(x_32, x_34, x_25, x_29);
x_3 = x_16;
x_4 = lean_box(0);
x_5 = x_35;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
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
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
}
}
lean_object* l___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Syntax_isNone(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_13, x_14);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Term_elabType(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l___private_Lean_Elab_Match_4__elabDiscrsWitMatchType(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
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
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
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
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
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
x_35 = x_1;
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__1), 9, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_35);
x_38 = x_37;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = lean_apply_7(x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_array_get_size(x_40);
x_43 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__3(x_40, x_40, x_42, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_5);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_40);
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
lean_object* l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_kabstract___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Elab_expandMacros___main(x_1, x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_12, x_2, x_19);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_20;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_26; uint8_t x_27; 
x_15 = lean_array_fget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_3, x_2, x_16);
x_26 = x_15;
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 2);
x_31 = x_29;
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_16);
lean_closure_set(x_32, 2, x_31);
x_33 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_9, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_st_ref_get(x_5, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_8, 1);
x_45 = lean_ctor_get(x_8, 2);
x_46 = lean_environment_main_module(x_39);
lean_inc(x_45);
lean_inc(x_44);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
x_48 = x_32;
x_49 = lean_apply_2(x_48, x_47, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_st_ref_take(x_5, x_42);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 3);
lean_dec(x_56);
lean_ctor_set(x_53, 3, x_51);
x_57 = lean_st_ref_set(x_5, x_53, x_54);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_ctor_set(x_26, 1, x_50);
x_18 = x_26;
x_19 = x_58;
goto block_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
x_61 = lean_ctor_get(x_53, 2);
x_62 = lean_ctor_get(x_53, 4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set(x_63, 3, x_51);
lean_ctor_set(x_63, 4, x_62);
x_64 = lean_st_ref_set(x_5, x_63, x_54);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_ctor_set(x_26, 1, x_50);
x_18 = x_26;
x_19 = x_65;
goto block_25;
}
}
else
{
lean_object* x_66; 
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
lean_dec(x_49);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_67, x_70, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_67);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_4);
x_76 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(x_42);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_81 = lean_ctor_get(x_26, 0);
x_82 = lean_ctor_get(x_26, 1);
x_83 = lean_ctor_get(x_26, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_26);
x_84 = x_82;
lean_inc(x_1);
x_85 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_85, 0, x_1);
lean_closure_set(x_85, 1, x_16);
lean_closure_set(x_85, 2, x_84);
x_86 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_st_ref_get(x_9, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_get(x_5, x_91);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 3);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_8, 1);
x_98 = lean_ctor_get(x_8, 2);
x_99 = lean_environment_main_module(x_92);
lean_inc(x_98);
lean_inc(x_97);
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_87);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_98);
x_101 = x_85;
x_102 = lean_apply_2(x_101, x_100, x_96);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_st_ref_take(x_5, x_95);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 4);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_104);
lean_ctor_set(x_113, 4, x_111);
x_114 = lean_st_ref_set(x_5, x_113, x_107);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_81);
lean_ctor_set(x_116, 1, x_103);
lean_ctor_set(x_116, 2, x_83);
x_18 = x_116;
x_19 = x_115;
goto block_25;
}
else
{
lean_object* x_117; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_102, 0);
lean_inc(x_117);
lean_dec(x_102);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_118, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
lean_dec(x_118);
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
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_4);
x_127 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(x_95);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_17, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_10 = x_19;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = x_1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3___boxed), 10, 3);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_13);
x_16 = x_15;
x_17 = lean_apply_7(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_17;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_isNone(x_3);
lean_inc(x_7);
x_9 = l_Lean_Syntax_getKind(x_7);
x_10 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_8 == 0)
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_mkMatchAltView(x_3, x_7);
lean_dec(x_7);
x_18 = lean_array_push(x_4, x_17);
x_2 = x_16;
x_4 = x_18;
goto _start;
}
}
else
{
lean_dec(x_3);
if (x_11 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
lean_inc(x_7);
x_25 = l_Lean_Elab_Term_mkMatchAltView(x_7, x_7);
x_26 = lean_array_push(x_4, x_25);
x_2 = x_24;
x_3 = x_7;
x_4 = x_26;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_7__getMatchAltsAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_7__getMatchAltsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_7__getMatchAltsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_7__getMatchAltsAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
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
x_10 = l___private_Lean_Elab_Match_7__getMatchAltsAux___main(x_8, x_4, x_5, x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_8__getMatchAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkInaccessible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_inaccessible");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkInaccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkInaccessible___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_mkInaccessible___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_mkInaccessible___closed__2;
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
lean_object* _init_l_Lean_Elab_Term_PatternVar_hasToString___closed__1() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MVarWithIdKind");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
x_3 = l_Lean_Parser_registerBuiltinNodeKind(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__1___rarg(x_1, x_2);
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
x_10 = l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
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
x_18 = l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
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
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getKind(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1);
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1() {
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
x_3 = l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inaccessible");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3() {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = lean_ctor_get(x_3, 6);
lean_inc(x_11);
lean_inc(x_11);
x_12 = l_Lean_Elab_getBetterRef(x_10, x_11);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_dec(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
x_14 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Elab_addMacroStack(x_1, x_11);
x_23 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_22, x_5, x_6, x_7, x_8, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_tag(x_23, 1);
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, constructor or constant marked with '[matchPattern]' expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_5);
x_19 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_binderInfo(x_20);
lean_dec(x_20);
x_23 = l_Lean_BinderInfo_isExplicit(x_22);
if (x_23 == 0)
{
x_3 = x_17;
x_11 = x_21;
goto _start;
}
else
{
lean_object* x_25; 
x_25 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_7);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg___lambda__1), 10, 3);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_1, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1;
x_14 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg(x_10, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous pattern, use fully qualified name, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_1);
x_11 = l_Lean_MessageData_ofList(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
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
lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(x_1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1;
x_2 = l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
lean_inc(x_5);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_resolveName(x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(x_15, x_12);
x_18 = l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_3);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
lean_free_object(x_13);
x_23 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_5);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l_List_filterAux___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__1(x_24, x_12);
x_27 = l_List_map___main___at_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___spec__2(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_3);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_30);
x_34 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_5);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 1);
x_37 = lean_ctor_get(x_13, 0);
lean_dec(x_37);
x_38 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2;
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_39);
return x_13;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
lean_dec(x_3);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_42);
return x_13;
}
else
{
lean_object* x_43; 
lean_dec(x_40);
lean_free_object(x_13);
x_43 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_5);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2;
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_3);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_3);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_48);
x_52 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_5);
return x_52;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_54 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_54;
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__3;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1;
return x_1;
}
}
uint8_t l___private_Lean_Elab_Match_16__isDone(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Match_16__isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_16__isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_17__finalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_17__finalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_17__finalize___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_17__finalize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_17__finalize___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_17__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_12 = l___private_Lean_Elab_Match_17__finalize___closed__3;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l___private_Lean_Elab_Match_17__finalize___closed__3;
x_17 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
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
x_24 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__3;
x_25 = lean_array_push(x_24, x_23);
x_26 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_ctor_get(x_1, 6);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_mkAppStx(x_27, x_28);
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
x_32 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__3;
x_33 = lean_array_push(x_32, x_31);
x_34 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_ctor_get(x_1, 6);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_mkAppStx(x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_17__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_17__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
uint8_t l___private_Lean_Elab_Match_18__isNextArgAccessible(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Match_18__isNextArgAccessible___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_18__isNextArgAccessible(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_19__getNextParam(lean_object* x_1) {
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
lean_object* _init_l___private_Lean_Elab_Match_20__pushNewArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_2 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_20__pushNewArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (x_2 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_array_push(x_15, x_13);
lean_ctor_set(x_3, 6, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get(x_3, 3);
x_24 = lean_ctor_get(x_3, 4);
x_25 = lean_ctor_get(x_3, 5);
x_26 = lean_ctor_get(x_3, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_27 = lean_array_push(x_26, x_13);
x_28 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set(x_28, 6, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 1, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
lean_dec(x_4);
x_31 = lean_apply_9(x_1, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_3, 6);
x_36 = lean_array_push(x_35, x_34);
lean_ctor_set(x_3, 6, x_36);
lean_ctor_set(x_31, 0, x_3);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_42 = lean_ctor_get(x_3, 2);
x_43 = lean_ctor_get(x_3, 3);
x_44 = lean_ctor_get(x_3, 4);
x_45 = lean_ctor_get(x_3, 5);
x_46 = lean_ctor_get(x_3, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_47 = lean_array_push(x_46, x_37);
x_48 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_44);
lean_ctor_set(x_48, 5, x_45);
lean_ctor_set(x_48, 6, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*7, x_40);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 1, x_41);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_49 = lean_ctor_get(x_31, 0);
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_31);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_54 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_55 = lean_ctor_get(x_3, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 6);
lean_inc(x_59);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_60 = x_3;
} else {
 lean_dec_ref(x_3);
 x_60 = lean_box(0);
}
x_61 = lean_array_push(x_59, x_49);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 7, 2);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*7, x_53);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 1, x_54);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_50);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
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
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = l___private_Lean_Elab_Match_20__pushNewArg___closed__1;
x_69 = l_unreachable_x21___rarg(x_68);
x_70 = lean_apply_8(x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_70;
}
}
}
lean_object* l___private_Lean_Elab_Match_20__pushNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_21__processExplicitArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_21__processExplicitArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_dec(x_3);
x_15 = x_14;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_16, x_15);
x_18 = x_17;
x_19 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_20 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_19);
x_21 = l_Array_HasRepr___rarg___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Elab_Match_21__processExplicitArg___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_Match_21__processExplicitArg___closed__4;
x_33 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_2, x_3, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_3, 5);
lean_dec(x_35);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
lean_ctor_set(x_3, 5, x_37);
x_38 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_2, x_3, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_ctor_get(x_3, 3);
x_45 = lean_ctor_get(x_3, 4);
x_46 = lean_ctor_get(x_3, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_dec(x_12);
x_49 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*7, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 1, x_42);
x_50 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_2, x_49, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_50;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_21__processExplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_Match_21__processExplicitArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_22__processImplicitArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_17 = l___private_Lean_Elab_Match_21__processExplicitArg___closed__4;
x_18 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_2, x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l___private_Lean_Elab_Match_21__processExplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_Match_22__processImplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_Match_22__processImplicitArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_23__processCtorAppAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_23__processCtorAppAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l___private_Lean_Elab_Match_16__isDone(x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = l___private_Lean_Elab_Match_18__isNextArgAccessible(x_2);
x_13 = l___private_Lean_Elab_Match_19__getNextParam(x_2);
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
x_26 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_23__processCtorAppAux___main___spec__1(x_15, x_22, x_25);
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
x_29 = l___private_Lean_Elab_Match_22__processImplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l___private_Lean_Elab_Match_22__processImplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_45 = l___private_Lean_Elab_Match_21__processExplicitArg(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_66 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_12, x_14, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_80 = l___private_Lean_Elab_Match_20__pushNewArg(x_1, x_12, x_78, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_88 = l___private_Lean_Elab_Match_17__finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_88;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_23__processCtorAppAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_23__processCtorAppAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_23__processCtorAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_23__processCtorAppAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
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
x_17 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_3);
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
x_28 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = l_Lean_Expr_fvarId_x21(x_1);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
x_20 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_16, 2, x_20);
x_21 = lean_st_ref_set(x_8, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_5);
x_23 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_10, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = l_Lean_TraceState_Inhabited___closed__1;
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_st_ref_set(x_8, x_41, x_17);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_5);
x_44 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_10, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_5);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_5);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
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
lean_dec(x_4);
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
lean_inc(x_4);
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
lean_dec(x_4);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___spec__4___rarg___lambda__1), 11, 4);
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
if (lean_obj_tag(x_8) == 6)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Array_empty___closed__1;
x_42 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_24);
lean_ctor_set(x_42, 3, x_20);
lean_ctor_set(x_42, 4, x_5);
lean_ctor_set(x_42, 5, x_6);
lean_ctor_set(x_42, 6, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*7, x_3);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 1, x_4);
x_43 = l___private_Lean_Elab_Match_23__processCtorAppAux___main(x_7, x_42, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_25);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_box(0);
x_26 = x_44;
goto block_38;
}
block_38:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_26);
x_27 = lean_st_ref_get(x_17, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_matchPatternAttr;
x_32 = l_Lean_TagAttribute_hasTag(x_31, x_30, x_1);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_33 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_box(0);
x_35 = l_Array_empty___closed__1;
x_36 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_20);
lean_ctor_set(x_36, 4, x_5);
lean_ctor_set(x_36, 5, x_6);
lean_ctor_set(x_36, 6, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*7, x_3);
lean_ctor_set_uint8(x_36, sizeof(void*)*7 + 1, x_4);
x_37 = l___private_Lean_Elab_Match_23__processCtorAppAux___main(x_7, x_36, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_29);
return x_37;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_23);
if (x_45 == 0)
{
return x_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_23);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_44; uint8_t x_45; 
x_14 = l_Array_toList___rarg(x_4);
x_44 = l_Lean_identKind___closed__2;
lean_inc(x_2);
x_45 = l_Lean_Syntax_isOfKind(x_2, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_inc(x_2);
x_47 = l_Lean_Syntax_isOfKind(x_2, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_49 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_Lean_Syntax_getArgs(x_2);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_dec_eq(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_59 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_58, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Syntax_getArg(x_2, x_64);
lean_dec(x_2);
lean_inc(x_65);
x_66 = l_Lean_Syntax_isOfKind(x_65, x_44);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_65);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_67 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_68 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_67, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
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
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_73 = 1;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_74);
x_15 = x_75;
x_16 = x_13;
goto block_43;
}
}
}
}
else
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_77);
x_15 = x_78;
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
lean_inc(x_9);
lean_inc(x_7);
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
x_22 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_inc(x_7);
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
lean_closure_set(x_31, 0, x_25);
lean_closure_set(x_31, 1, x_17);
lean_closure_set(x_31, 2, x_18);
lean_closure_set(x_31, 3, x_30);
lean_closure_set(x_31, 4, x_3);
lean_closure_set(x_31, 5, x_14);
lean_closure_set(x_31, 6, x_1);
lean_closure_set(x_31, 7, x_27);
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
x_38 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = l_Lean_Elab_Term_CollectPatternVars_CtorApp_processCtorApp___lambda__1(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_8);
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
lean_inc(x_13);
x_14 = l_Lean_Elab_getBetterRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
lean_dec(x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_13);
x_16 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Elab_addMacroStack(x_2, x_13);
x_25 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_24, x_6, x_7, x_8, x_9, x_10);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, variable '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__processVar___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__processVar___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurred more than once");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__processVar___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__processVar___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern variable, must be atomic");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__processVar___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__processVar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__processVar___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_24__processVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_54; 
x_54 = l_Lean_Syntax_isIdent(x_1);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_56 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_1, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
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
else
{
x_10 = x_9;
goto block_53;
}
block_53:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_42; uint8_t x_43; 
x_11 = l_Lean_Syntax_getId(x_1);
x_42 = l_Lean_Name_eraseMacroScopes(x_11);
x_43 = l_Lean_Name_isAtomic(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_1);
x_44 = l___private_Lean_Elab_Match_24__processVar___closed__9;
x_45 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
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
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_st_ref_get(x_2, x_10);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_12 = x_51;
x_13 = x_52;
goto block_41;
}
block_41:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_NameSet_contains(x_14, x_11);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_3);
x_16 = lean_st_ref_take(x_2, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_box(0);
lean_inc(x_11);
x_21 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_19, x_11, x_20);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_11);
x_24 = lean_array_push(x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_st_ref_set(x_2, x_25, x_18);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_1);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_11);
x_32 = l___private_Lean_Elab_Match_24__processVar___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Match_24__processVar___closed__6;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
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
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_24__processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_24__processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_25__processId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_6);
lean_inc(x_4);
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
x_18 = l___private_Lean_Elab_Match_24__processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_21);
lean_inc(x_14);
x_28 = lean_environment_find(x_14, x_21);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 6)
{
lean_object* x_31; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_14);
x_31 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_30);
x_32 = lean_box(0);
x_22 = x_32;
goto block_27;
}
}
block_27:
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_22);
x_23 = l_Lean_matchPatternAttr;
x_24 = l_Lean_TagAttribute_hasTag(x_23, x_14, x_21);
lean_dec(x_21);
lean_dec(x_14);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = l___private_Lean_Elab_Match_24__processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_26;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_dec(x_15);
x_34 = l___private_Lean_Elab_Match_24__processVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_34;
}
}
}
else
{
uint8_t x_35; 
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
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.anonymous");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.str");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("str");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExpr___closed__1;
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Name_toExprAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9;
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.num");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__14;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExpr___closed__1;
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9;
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__18;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Name_toExprAux___main___closed__1;
x_16 = lean_name_mk_string(x_1, x_15);
x_17 = l_Lean_Name_toExprAux___main___closed__2;
x_18 = lean_name_mk_string(x_16, x_17);
x_19 = l_Lean_addMacroScope(x_14, x_18, x_10);
x_20 = l_Lean_mkAppStx___closed__1;
x_21 = lean_name_mk_string(x_1, x_20);
x_22 = lean_name_mk_string(x_21, x_15);
x_23 = lean_name_mk_string(x_22, x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_SourceInfo_inhabited___closed__1;
x_28 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3;
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_12, 0, x_29);
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = l_Lean_Name_toExprAux___main___closed__1;
x_33 = lean_name_mk_string(x_1, x_32);
x_34 = l_Lean_Name_toExprAux___main___closed__2;
x_35 = lean_name_mk_string(x_33, x_34);
x_36 = l_Lean_addMacroScope(x_30, x_35, x_10);
x_37 = l_Lean_mkAppStx___closed__1;
x_38 = lean_name_mk_string(x_1, x_37);
x_39 = lean_name_mk_string(x_38, x_32);
x_40 = lean_name_mk_string(x_39, x_34);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_SourceInfo_inhabited___closed__1;
x_45 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3;
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_31);
return x_47;
}
}
case 1:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l___private_Lean_Elab_Match_26__nameToPattern___main(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8;
x_60 = l_Lean_addMacroScope(x_58, x_59, x_54);
x_61 = l_Lean_SourceInfo_inhabited___closed__1;
x_62 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6;
x_63 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12;
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_63);
x_65 = l_Array_empty___closed__1;
x_66 = lean_array_push(x_65, x_64);
x_67 = lean_array_push(x_65, x_51);
x_68 = l_Lean_mkStxStrLit(x_49, x_61);
x_69 = lean_array_push(x_67, x_68);
x_70 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_71 = lean_array_push(x_69, x_70);
x_72 = l_Lean_nullKind___closed__2;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_66, x_73);
x_75 = l_Lean_mkAppStx___closed__8;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_56, 0, x_76);
return x_56;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_77 = lean_ctor_get(x_56, 0);
x_78 = lean_ctor_get(x_56, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_56);
x_79 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8;
x_80 = l_Lean_addMacroScope(x_77, x_79, x_54);
x_81 = l_Lean_SourceInfo_inhabited___closed__1;
x_82 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6;
x_83 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12;
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_83);
x_85 = l_Array_empty___closed__1;
x_86 = lean_array_push(x_85, x_84);
x_87 = lean_array_push(x_85, x_51);
x_88 = l_Lean_mkStxStrLit(x_49, x_81);
x_89 = lean_array_push(x_87, x_88);
x_90 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_91 = lean_array_push(x_89, x_90);
x_92 = l_Lean_nullKind___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_86, x_93);
x_95 = l_Lean_mkAppStx___closed__8;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_78);
return x_97;
}
}
default: 
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
lean_dec(x_1);
x_100 = l___private_Lean_Elab_Match_26__nameToPattern___main(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17;
x_110 = l_Lean_addMacroScope(x_108, x_109, x_104);
x_111 = l_Lean_SourceInfo_inhabited___closed__1;
x_112 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15;
x_113 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20;
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_113);
x_115 = l_Array_empty___closed__1;
x_116 = lean_array_push(x_115, x_114);
x_117 = lean_array_push(x_115, x_101);
x_118 = l_Nat_repr(x_99);
x_119 = l_Lean_numLitKind;
x_120 = l_Lean_mkStxLit(x_119, x_118, x_111);
x_121 = lean_array_push(x_117, x_120);
x_122 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_123 = lean_array_push(x_121, x_122);
x_124 = l_Lean_nullKind___closed__2;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_push(x_116, x_125);
x_127 = l_Lean_mkAppStx___closed__8;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_106, 0, x_128);
return x_106;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_129 = lean_ctor_get(x_106, 0);
x_130 = lean_ctor_get(x_106, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_106);
x_131 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17;
x_132 = l_Lean_addMacroScope(x_129, x_131, x_104);
x_133 = l_Lean_SourceInfo_inhabited___closed__1;
x_134 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15;
x_135 = l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20;
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_132);
lean_ctor_set(x_136, 3, x_135);
x_137 = l_Array_empty___closed__1;
x_138 = lean_array_push(x_137, x_136);
x_139 = lean_array_push(x_137, x_101);
x_140 = l_Nat_repr(x_99);
x_141 = l_Lean_numLitKind;
x_142 = l_Lean_mkStxLit(x_141, x_140, x_133);
x_143 = lean_array_push(x_139, x_142);
x_144 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_145 = lean_array_push(x_143, x_144);
x_146 = l_Lean_nullKind___closed__2;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_array_push(x_138, x_147);
x_149 = l_Lean_mkAppStx___closed__8;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_130);
return x_151;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_26__nameToPattern___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_26__nameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_26__nameToPattern___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_26__nameToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_26__nameToPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_27__quotedNameToPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_27__quotedNameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_27__quotedNameToPattern___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Match_26__nameToPattern___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_14;
}
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_27__quotedNameToPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_Match_27__quotedNameToPattern___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_27__quotedNameToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_27__quotedNameToPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_28__collect___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_28__collect___main___spec__2(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_28__collect___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l___private_Lean_Elab_Match_28__collect___main(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymousCtor");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Match_28__collect___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, notation is ambiguous");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_28__collect___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_28__collect___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__11;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__11;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_28__collect___main___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_28__collect___main___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_28__collect___main), 9, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid struct instance pattern, 'with' is not allowed in patterns");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_28__collect___main___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_28__collect___main___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_28__collect___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_28__collect___main___lambda__1), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_28__collect___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_replaceRef(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_ctor_set(x_7, 3, x_18);
x_19 = lean_st_ref_take(x_4, x_9);
if (x_13 == 0)
{
lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; 
x_1059 = lean_ctor_get(x_19, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_19, 1);
lean_inc(x_1060);
lean_dec(x_19);
x_1061 = 0;
x_20 = x_1061;
x_21 = x_1059;
x_22 = x_1060;
goto block_1058;
}
else
{
lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; 
x_1062 = lean_ctor_get(x_19, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_19, 1);
lean_inc(x_1063);
lean_dec(x_19);
x_1064 = 1;
x_20 = x_1064;
x_21 = x_1062;
x_22 = x_1063;
goto block_1058;
}
block_1058:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_21, 3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_ctor_set(x_21, 3, x_26);
x_27 = lean_st_ref_set(x_4, x_21, x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_3, 7);
lean_dec(x_32);
lean_ctor_set(x_3, 7, x_24);
if (x_20 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l___private_Lean_Elab_Match_28__collect___main___closed__2;
x_34 = lean_name_eq(x_10, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_36 = lean_name_eq(x_10, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_mkHole___closed__2;
x_38 = lean_name_eq(x_10, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_40 = lean_name_eq(x_10, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_11);
x_41 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
x_42 = lean_name_eq(x_10, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
x_44 = lean_name_eq(x_10, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_46 = lean_name_eq(x_10, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_strLitKind;
x_48 = lean_name_eq(x_10, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_numLitKind;
x_50 = lean_name_eq(x_10, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_charLitKind;
x_52 = lean_name_eq(x_10, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_free_object(x_27);
x_53 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
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
x_57 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l___private_Lean_Elab_Match_28__collect___main___closed__5;
x_59 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_2);
x_60 = l___private_Lean_Elab_Match_27__quotedNameToPattern(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
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
lean_ctor_set(x_27, 0, x_1);
return x_27;
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
lean_ctor_set(x_27, 0, x_1);
return x_27;
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
lean_ctor_set(x_27, 0, x_1);
return x_27;
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
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_27);
lean_dec(x_10);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Syntax_getArg(x_1, x_61);
lean_inc(x_3);
lean_inc(x_62);
x_63 = l___private_Lean_Elab_Match_24__processVar(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
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
x_70 = l___private_Lean_Elab_Match_28__collect___main(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
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
x_79 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_80 = l_Lean_addMacroScope(x_78, x_79, x_74);
x_81 = l_Lean_SourceInfo_inhabited___closed__1;
x_82 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_83 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
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
x_94 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_95 = l_Lean_addMacroScope(x_92, x_94, x_74);
x_96 = l_Lean_SourceInfo_inhabited___closed__1;
x_97 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_98 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
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
x_112 = l___private_Lean_Elab_Match_28__collect___main(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
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
x_122 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_123 = l_Lean_addMacroScope(x_119, x_122, x_116);
x_124 = l_Lean_SourceInfo_inhabited___closed__1;
x_125 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_126 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
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
lean_free_object(x_27);
lean_dec(x_10);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Syntax_getArg(x_1, x_145);
lean_dec(x_1);
x_147 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_148 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_147, x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = l_Lean_Syntax_inhabited;
x_150 = lean_array_get(x_149, x_11, x_25);
x_151 = l_Lean_Syntax_isNone(x_150);
if (x_151 == 0)
{
uint8_t x_152; 
lean_free_object(x_27);
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
x_157 = l_Lean_Syntax_getArg(x_150, x_25);
x_158 = l_Lean_Syntax_isNone(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = l_Lean_Syntax_getArg(x_157, x_155);
x_160 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_inc(x_159);
x_161 = l_Lean_Syntax_isOfKind(x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_162 = l___private_Lean_Elab_Match_28__collect___main(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Syntax_setArg(x_150, x_155, x_163);
x_166 = l_Lean_Syntax_getArg(x_159, x_25);
x_167 = l_Lean_Syntax_getArgs(x_166);
lean_dec(x_166);
x_168 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_169 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_167, x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_164);
lean_dec(x_167);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_171);
lean_ctor_set(x_1, 0, x_172);
x_173 = l_Lean_Syntax_setArg(x_159, x_25, x_1);
x_174 = l_Lean_Syntax_setArg(x_157, x_155, x_173);
x_175 = l_Lean_Syntax_setArg(x_165, x_25, x_174);
x_176 = lean_array_set(x_11, x_25, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_10);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_169, 0, x_177);
return x_169;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_169, 0);
x_179 = lean_ctor_get(x_169, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_169);
x_180 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_180);
x_181 = l_Lean_Syntax_setArg(x_159, x_25, x_1);
x_182 = l_Lean_Syntax_setArg(x_157, x_155, x_181);
x_183 = l_Lean_Syntax_setArg(x_165, x_25, x_182);
x_184 = lean_array_set(x_11, x_25, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_10);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_179);
return x_186;
}
}
else
{
uint8_t x_187; 
lean_dec(x_165);
lean_dec(x_159);
lean_dec(x_157);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_187 = !lean_is_exclusive(x_169);
if (x_187 == 0)
{
return x_169;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_169, 0);
x_189 = lean_ctor_get(x_169, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_169);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
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
x_191 = !lean_is_exclusive(x_162);
if (x_191 == 0)
{
return x_162;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_162, 0);
x_193 = lean_ctor_get(x_162, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_162);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_object* x_195; 
lean_dec(x_159);
lean_dec(x_157);
x_195 = l___private_Lean_Elab_Match_28__collect___main(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = l_Lean_Syntax_setArg(x_150, x_155, x_197);
x_199 = lean_array_set(x_11, x_25, x_198);
lean_ctor_set(x_1, 1, x_199);
lean_ctor_set(x_195, 0, x_1);
return x_195;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_195, 0);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_195);
x_202 = l_Lean_Syntax_setArg(x_150, x_155, x_200);
x_203 = lean_array_set(x_11, x_25, x_202);
lean_ctor_set(x_1, 1, x_203);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_1);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
}
else
{
uint8_t x_205; 
lean_free_object(x_1);
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_205 = !lean_is_exclusive(x_195);
if (x_205 == 0)
{
return x_195;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_195, 0);
x_207 = lean_ctor_get(x_195, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_195);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
else
{
lean_object* x_209; 
lean_dec(x_157);
x_209 = l___private_Lean_Elab_Match_28__collect___main(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = l_Lean_Syntax_setArg(x_150, x_155, x_211);
x_213 = lean_array_set(x_11, x_25, x_212);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_209, 0, x_1);
return x_209;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_209, 0);
x_215 = lean_ctor_get(x_209, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_209);
x_216 = l_Lean_Syntax_setArg(x_150, x_155, x_214);
x_217 = lean_array_set(x_11, x_25, x_216);
lean_ctor_set(x_1, 1, x_217);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_215);
return x_218;
}
}
else
{
uint8_t x_219; 
lean_free_object(x_1);
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_219 = !lean_is_exclusive(x_209);
if (x_219 == 0)
{
return x_209;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_209, 0);
x_221 = lean_ctor_get(x_209, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_209);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_1);
x_223 = lean_unsigned_to_nat(0u);
x_224 = l_Lean_Syntax_getArg(x_150, x_223);
x_225 = l_Lean_Syntax_getArg(x_150, x_25);
x_226 = l_Lean_Syntax_isNone(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_227 = l_Lean_Syntax_getArg(x_225, x_223);
x_228 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_inc(x_227);
x_229 = l_Lean_Syntax_isOfKind(x_227, x_228);
if (x_229 == 0)
{
lean_object* x_230; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_230 = l___private_Lean_Elab_Match_28__collect___main(x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_Syntax_setArg(x_150, x_223, x_231);
x_234 = l_Lean_Syntax_getArg(x_227, x_25);
x_235 = l_Lean_Syntax_getArgs(x_234);
lean_dec(x_234);
x_236 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_237 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_235, x_236, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_232);
lean_dec(x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
x_241 = l_Lean_nullKind;
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
x_243 = l_Lean_Syntax_setArg(x_227, x_25, x_242);
x_244 = l_Lean_Syntax_setArg(x_225, x_223, x_243);
x_245 = l_Lean_Syntax_setArg(x_233, x_25, x_244);
x_246 = lean_array_set(x_11, x_25, x_245);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_10);
lean_ctor_set(x_247, 1, x_246);
if (lean_is_scalar(x_240)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_240;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_239);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_233);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_11);
lean_dec(x_10);
x_249 = lean_ctor_get(x_237, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_237, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_251 = x_237;
} else {
 lean_dec_ref(x_237);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_227);
lean_dec(x_225);
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
x_253 = lean_ctor_get(x_230, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_230, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_255 = x_230;
} else {
 lean_dec_ref(x_230);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; 
lean_dec(x_227);
lean_dec(x_225);
x_257 = l___private_Lean_Elab_Match_28__collect___main(x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_260 = x_257;
} else {
 lean_dec_ref(x_257);
 x_260 = lean_box(0);
}
x_261 = l_Lean_Syntax_setArg(x_150, x_223, x_258);
x_262 = lean_array_set(x_11, x_25, x_261);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_10);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_260)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_260;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_259);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_265 = lean_ctor_get(x_257, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_257, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_267 = x_257;
} else {
 lean_dec_ref(x_257);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
else
{
lean_object* x_269; 
lean_dec(x_225);
x_269 = l___private_Lean_Elab_Match_28__collect___main(x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_272 = x_269;
} else {
 lean_dec_ref(x_269);
 x_272 = lean_box(0);
}
x_273 = l_Lean_Syntax_setArg(x_150, x_223, x_270);
x_274 = lean_array_set(x_11, x_25, x_273);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_10);
lean_ctor_set(x_275, 1, x_274);
if (lean_is_scalar(x_272)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_272;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_271);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
x_277 = lean_ctor_get(x_269, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_269, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_279 = x_269;
} else {
 lean_dec_ref(x_269);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
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
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
lean_dec(x_3);
lean_free_object(x_27);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_281 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_29);
lean_dec(x_8);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_st_ref_take(x_2, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = !lean_is_exclusive(x_285);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_288 = lean_ctor_get(x_285, 1);
x_289 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_282);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = lean_array_push(x_288, x_290);
lean_ctor_set(x_285, 1, x_291);
x_292 = lean_st_ref_set(x_2, x_285, x_286);
lean_dec(x_2);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_292, 0);
lean_dec(x_294);
lean_ctor_set(x_292, 0, x_282);
return x_292;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
lean_dec(x_292);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_282);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_297 = lean_ctor_get(x_285, 0);
x_298 = lean_ctor_get(x_285, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_285);
x_299 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_282);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_array_push(x_298, x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_297);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_st_ref_set(x_2, x_302, x_286);
lean_dec(x_2);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_282);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
else
{
uint8_t x_307; 
lean_free_object(x_27);
x_307 = !lean_is_exclusive(x_1);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_308 = lean_ctor_get(x_1, 1);
lean_dec(x_308);
x_309 = lean_ctor_get(x_1, 0);
lean_dec(x_309);
x_310 = l_Lean_Syntax_inhabited;
x_311 = lean_array_get(x_310, x_11, x_25);
x_312 = l_Lean_Syntax_isNone(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_313 = l___private_Lean_Elab_Match_28__collect___main___closed__14;
x_314 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_311, x_313, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_311);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
return x_314;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_314, 0);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_314);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_311);
x_319 = lean_unsigned_to_nat(2u);
x_320 = lean_array_get(x_310, x_11, x_319);
x_321 = l_Lean_Syntax_getArgs(x_320);
lean_dec(x_320);
x_322 = l___private_Lean_Elab_Match_28__collect___main___closed__15;
x_323 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_321, x_322, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_321);
if (lean_obj_tag(x_323) == 0)
{
uint8_t x_324; 
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_323, 0);
x_326 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_325);
lean_ctor_set(x_1, 0, x_326);
x_327 = lean_array_set(x_11, x_319, x_1);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_10);
lean_ctor_set(x_328, 1, x_327);
lean_ctor_set(x_323, 0, x_328);
return x_323;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_ctor_get(x_323, 0);
x_330 = lean_ctor_get(x_323, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_323);
x_331 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_329);
lean_ctor_set(x_1, 0, x_331);
x_332 = lean_array_set(x_11, x_319, x_1);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_10);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_330);
return x_334;
}
}
else
{
uint8_t x_335; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_335 = !lean_is_exclusive(x_323);
if (x_335 == 0)
{
return x_323;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_323, 0);
x_337 = lean_ctor_get(x_323, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_323);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_dec(x_1);
x_339 = l_Lean_Syntax_inhabited;
x_340 = lean_array_get(x_339, x_11, x_25);
x_341 = l_Lean_Syntax_isNone(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_11);
lean_dec(x_10);
x_342 = l___private_Lean_Elab_Match_28__collect___main___closed__14;
x_343 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_340, x_342, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_340);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_340);
x_348 = lean_unsigned_to_nat(2u);
x_349 = lean_array_get(x_339, x_11, x_348);
x_350 = l_Lean_Syntax_getArgs(x_349);
lean_dec(x_349);
x_351 = l___private_Lean_Elab_Match_28__collect___main___closed__15;
x_352 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_350, x_351, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
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
x_358 = lean_array_set(x_11, x_348, x_357);
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
}
else
{
uint8_t x_365; 
lean_free_object(x_27);
x_365 = !lean_is_exclusive(x_1);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_366 = lean_ctor_get(x_1, 1);
lean_dec(x_366);
x_367 = lean_ctor_get(x_1, 0);
lean_dec(x_367);
x_368 = l_Lean_Syntax_inhabited;
x_369 = lean_array_get(x_368, x_11, x_25);
x_370 = l_Lean_Syntax_getArgs(x_369);
lean_dec(x_369);
x_371 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_372 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_370, x_371, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_370);
if (lean_obj_tag(x_372) == 0)
{
uint8_t x_373; 
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_372, 0);
x_375 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_374);
lean_ctor_set(x_1, 0, x_375);
x_376 = lean_array_set(x_11, x_25, x_1);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_10);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set(x_372, 0, x_377);
return x_372;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_378 = lean_ctor_get(x_372, 0);
x_379 = lean_ctor_get(x_372, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_372);
x_380 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_378);
lean_ctor_set(x_1, 0, x_380);
x_381 = lean_array_set(x_11, x_25, x_1);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_10);
lean_ctor_set(x_382, 1, x_381);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_379);
return x_383;
}
}
else
{
uint8_t x_384; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_384 = !lean_is_exclusive(x_372);
if (x_384 == 0)
{
return x_372;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_372, 0);
x_386 = lean_ctor_get(x_372, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_372);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_1);
x_388 = l_Lean_Syntax_inhabited;
x_389 = lean_array_get(x_388, x_11, x_25);
x_390 = l_Lean_Syntax_getArgs(x_389);
lean_dec(x_389);
x_391 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_392 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_390, x_391, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_390);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_395 = x_392;
} else {
 lean_dec_ref(x_392);
 x_395 = lean_box(0);
}
x_396 = l_Lean_nullKind;
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_393);
x_398 = lean_array_set(x_11, x_25, x_397);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_10);
lean_ctor_set(x_399, 1, x_398);
if (lean_is_scalar(x_395)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_395;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_394);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_11);
lean_dec(x_10);
x_401 = lean_ctor_get(x_392, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_392, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_403 = x_392;
} else {
 lean_dec_ref(x_392);
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
}
}
else
{
lean_object* x_405; lean_object* x_406; 
lean_free_object(x_27);
lean_dec(x_11);
lean_dec(x_10);
x_405 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_406 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_405, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_1);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; uint8_t x_415; uint8_t x_416; lean_object* x_417; 
x_407 = lean_ctor_get(x_3, 0);
x_408 = lean_ctor_get(x_3, 1);
x_409 = lean_ctor_get(x_3, 2);
x_410 = lean_ctor_get(x_3, 3);
x_411 = lean_ctor_get(x_3, 4);
x_412 = lean_ctor_get(x_3, 5);
x_413 = lean_ctor_get(x_3, 6);
x_414 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_415 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_416 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_3);
x_417 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_417, 0, x_407);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_410);
lean_ctor_set(x_417, 4, x_411);
lean_ctor_set(x_417, 5, x_412);
lean_ctor_set(x_417, 6, x_413);
lean_ctor_set(x_417, 7, x_24);
lean_ctor_set_uint8(x_417, sizeof(void*)*8, x_414);
lean_ctor_set_uint8(x_417, sizeof(void*)*8 + 1, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*8 + 2, x_416);
if (x_20 == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = l___private_Lean_Elab_Match_28__collect___main___closed__2;
x_419 = lean_name_eq(x_10, x_418);
if (x_419 == 0)
{
lean_object* x_420; uint8_t x_421; 
x_420 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_421 = lean_name_eq(x_10, x_420);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; 
x_422 = l_Lean_mkHole___closed__2;
x_423 = lean_name_eq(x_10, x_422);
if (x_423 == 0)
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_425 = lean_name_eq(x_10, x_424);
if (x_425 == 0)
{
lean_object* x_426; uint8_t x_427; 
lean_dec(x_11);
x_426 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
x_427 = lean_name_eq(x_10, x_426);
if (x_427 == 0)
{
lean_object* x_428; uint8_t x_429; 
x_428 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
x_429 = lean_name_eq(x_10, x_428);
if (x_429 == 0)
{
lean_object* x_430; uint8_t x_431; 
x_430 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_431 = lean_name_eq(x_10, x_430);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = l_Lean_strLitKind;
x_433 = lean_name_eq(x_10, x_432);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = l_Lean_numLitKind;
x_435 = lean_name_eq(x_10, x_434);
if (x_435 == 0)
{
lean_object* x_436; uint8_t x_437; 
x_436 = l_Lean_charLitKind;
x_437 = lean_name_eq(x_10, x_436);
if (x_437 == 0)
{
lean_object* x_438; uint8_t x_439; 
lean_free_object(x_27);
x_438 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_439 = lean_name_eq(x_10, x_438);
if (x_439 == 0)
{
lean_object* x_440; uint8_t x_441; 
lean_dec(x_1);
x_440 = l_Lean_choiceKind;
x_441 = lean_name_eq(x_10, x_440);
lean_dec(x_10);
if (x_441 == 0)
{
lean_object* x_442; 
x_442 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; 
x_443 = l___private_Lean_Elab_Match_28__collect___main___closed__5;
x_444 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_443, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_444;
}
}
else
{
lean_object* x_445; 
lean_dec(x_10);
lean_dec(x_2);
x_445 = l___private_Lean_Elab_Match_27__quotedNameToPattern(x_1, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_445;
}
}
else
{
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_free_object(x_27);
lean_dec(x_10);
x_446 = lean_unsigned_to_nat(0u);
x_447 = l_Lean_Syntax_getArg(x_1, x_446);
lean_inc(x_417);
lean_inc(x_447);
x_448 = l___private_Lean_Elab_Match_24__processVar(x_447, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_450 = lean_unsigned_to_nat(2u);
x_451 = l_Lean_Syntax_getArg(x_1, x_450);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_452 = x_1;
} else {
 lean_dec_ref(x_1);
 x_452 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_417);
x_453 = l___private_Lean_Elab_Match_28__collect___main(x_451, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_449);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = l_Lean_Elab_Term_getCurrMacroScope(x_417, x_4, x_5, x_6, x_7, x_8, x_455);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_417);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_458);
lean_dec(x_8);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_462 = x_459;
} else {
 lean_dec_ref(x_459);
 x_462 = lean_box(0);
}
x_463 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_464 = l_Lean_addMacroScope(x_460, x_463, x_457);
x_465 = l_Lean_SourceInfo_inhabited___closed__1;
x_466 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_467 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
x_468 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
lean_ctor_set(x_468, 2, x_464);
lean_ctor_set(x_468, 3, x_467);
x_469 = l_Array_empty___closed__1;
x_470 = lean_array_push(x_469, x_468);
x_471 = lean_array_push(x_469, x_447);
x_472 = lean_array_push(x_471, x_454);
x_473 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_452)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_452;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_472);
x_475 = lean_array_push(x_470, x_474);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_12);
lean_ctor_set(x_476, 1, x_475);
if (lean_is_scalar(x_462)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_462;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_461);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_478 = lean_ctor_get(x_453, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_453, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_480 = x_453;
} else {
 lean_dec_ref(x_453);
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
lean_dec(x_447);
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_482 = lean_ctor_get(x_448, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_448, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_484 = x_448;
} else {
 lean_dec_ref(x_448);
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
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_free_object(x_27);
lean_dec(x_10);
x_486 = lean_unsigned_to_nat(0u);
x_487 = l_Lean_Syntax_getArg(x_1, x_486);
lean_dec(x_1);
x_488 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_489 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_488, x_487, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
return x_489;
}
}
else
{
lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_490 = l_Lean_Syntax_inhabited;
x_491 = lean_array_get(x_490, x_11, x_25);
x_492 = l_Lean_Syntax_isNone(x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_493 = x_1;
} else {
 lean_dec_ref(x_1);
 x_493 = lean_box(0);
}
x_494 = lean_unsigned_to_nat(0u);
x_495 = l_Lean_Syntax_getArg(x_491, x_494);
x_496 = l_Lean_Syntax_getArg(x_491, x_25);
x_497 = l_Lean_Syntax_isNone(x_496);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_498 = l_Lean_Syntax_getArg(x_496, x_494);
x_499 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_inc(x_498);
x_500 = l_Lean_Syntax_isOfKind(x_498, x_499);
if (x_500 == 0)
{
lean_object* x_501; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_417);
lean_inc(x_2);
x_501 = l___private_Lean_Elab_Match_28__collect___main(x_495, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_504 = l_Lean_Syntax_setArg(x_491, x_494, x_502);
x_505 = l_Lean_Syntax_getArg(x_498, x_25);
x_506 = l_Lean_Syntax_getArgs(x_505);
lean_dec(x_505);
x_507 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_508 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_506, x_507, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_503);
lean_dec(x_506);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_511 = x_508;
} else {
 lean_dec_ref(x_508);
 x_511 = lean_box(0);
}
x_512 = l_Lean_nullKind;
if (lean_is_scalar(x_493)) {
 x_513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_513 = x_493;
}
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_509);
x_514 = l_Lean_Syntax_setArg(x_498, x_25, x_513);
x_515 = l_Lean_Syntax_setArg(x_496, x_494, x_514);
x_516 = l_Lean_Syntax_setArg(x_504, x_25, x_515);
x_517 = lean_array_set(x_11, x_25, x_516);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_10);
lean_ctor_set(x_518, 1, x_517);
if (lean_is_scalar(x_511)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_511;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_510);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_504);
lean_dec(x_498);
lean_dec(x_496);
lean_dec(x_493);
lean_dec(x_11);
lean_dec(x_10);
x_520 = lean_ctor_get(x_508, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_508, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_522 = x_508;
} else {
 lean_dec_ref(x_508);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_498);
lean_dec(x_496);
lean_dec(x_493);
lean_dec(x_491);
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_524 = lean_ctor_get(x_501, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_501, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_526 = x_501;
} else {
 lean_dec_ref(x_501);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
else
{
lean_object* x_528; 
lean_dec(x_498);
lean_dec(x_496);
x_528 = l___private_Lean_Elab_Match_28__collect___main(x_495, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_531 = x_528;
} else {
 lean_dec_ref(x_528);
 x_531 = lean_box(0);
}
x_532 = l_Lean_Syntax_setArg(x_491, x_494, x_529);
x_533 = lean_array_set(x_11, x_25, x_532);
if (lean_is_scalar(x_493)) {
 x_534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_534 = x_493;
}
lean_ctor_set(x_534, 0, x_10);
lean_ctor_set(x_534, 1, x_533);
if (lean_is_scalar(x_531)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_531;
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_530);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_493);
lean_dec(x_491);
lean_dec(x_11);
lean_dec(x_10);
x_536 = lean_ctor_get(x_528, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_528, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_538 = x_528;
} else {
 lean_dec_ref(x_528);
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
lean_object* x_540; 
lean_dec(x_496);
x_540 = l___private_Lean_Elab_Match_28__collect___main(x_495, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
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
x_544 = l_Lean_Syntax_setArg(x_491, x_494, x_541);
x_545 = lean_array_set(x_11, x_25, x_544);
if (lean_is_scalar(x_493)) {
 x_546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_546 = x_493;
}
lean_ctor_set(x_546, 0, x_10);
lean_ctor_set(x_546, 1, x_545);
if (lean_is_scalar(x_543)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_543;
}
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_542);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_493);
lean_dec(x_491);
lean_dec(x_11);
lean_dec(x_10);
x_548 = lean_ctor_get(x_540, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_540, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_550 = x_540;
} else {
 lean_dec_ref(x_540);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
}
else
{
lean_dec(x_491);
lean_dec(x_417);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_417);
lean_free_object(x_27);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_552 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_29);
lean_dec(x_8);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_st_ref_take(x_2, x_554);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_ctor_get(x_556, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_556, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_560 = x_556;
} else {
 lean_dec_ref(x_556);
 x_560 = lean_box(0);
}
x_561 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_553);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_561);
x_563 = lean_array_push(x_559, x_562);
if (lean_is_scalar(x_560)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_560;
}
lean_ctor_set(x_564, 0, x_558);
lean_ctor_set(x_564, 1, x_563);
x_565 = lean_st_ref_set(x_2, x_564, x_557);
lean_dec(x_2);
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_567 = x_565;
} else {
 lean_dec_ref(x_565);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_553);
lean_ctor_set(x_568, 1, x_566);
return x_568;
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_569 = x_1;
} else {
 lean_dec_ref(x_1);
 x_569 = lean_box(0);
}
x_570 = l_Lean_Syntax_inhabited;
x_571 = lean_array_get(x_570, x_11, x_25);
x_572 = l_Lean_Syntax_isNone(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_569);
lean_dec(x_11);
lean_dec(x_10);
x_573 = l___private_Lean_Elab_Match_28__collect___main___closed__14;
x_574 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_571, x_573, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_571);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_577 = x_574;
} else {
 lean_dec_ref(x_574);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_575);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_571);
x_579 = lean_unsigned_to_nat(2u);
x_580 = lean_array_get(x_570, x_11, x_579);
x_581 = l_Lean_Syntax_getArgs(x_580);
lean_dec(x_580);
x_582 = l___private_Lean_Elab_Match_28__collect___main___closed__15;
x_583 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_581, x_582, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_581);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_586 = x_583;
} else {
 lean_dec_ref(x_583);
 x_586 = lean_box(0);
}
x_587 = l_Lean_nullKind;
if (lean_is_scalar(x_569)) {
 x_588 = lean_alloc_ctor(1, 2, 0);
} else {
 x_588 = x_569;
}
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_584);
x_589 = lean_array_set(x_11, x_579, x_588);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_10);
lean_ctor_set(x_590, 1, x_589);
if (lean_is_scalar(x_586)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_586;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_585);
return x_591;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_569);
lean_dec(x_11);
lean_dec(x_10);
x_592 = lean_ctor_get(x_583, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_583, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_594 = x_583;
} else {
 lean_dec_ref(x_583);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
}
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_596 = x_1;
} else {
 lean_dec_ref(x_1);
 x_596 = lean_box(0);
}
x_597 = l_Lean_Syntax_inhabited;
x_598 = lean_array_get(x_597, x_11, x_25);
x_599 = l_Lean_Syntax_getArgs(x_598);
lean_dec(x_598);
x_600 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_601 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_599, x_600, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_599);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
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
x_605 = l_Lean_nullKind;
if (lean_is_scalar(x_596)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_596;
}
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_602);
x_607 = lean_array_set(x_11, x_25, x_606);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_10);
lean_ctor_set(x_608, 1, x_607);
if (lean_is_scalar(x_604)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_604;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_603);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_596);
lean_dec(x_11);
lean_dec(x_10);
x_610 = lean_ctor_get(x_601, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_601, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_612 = x_601;
} else {
 lean_dec_ref(x_601);
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
else
{
lean_object* x_614; lean_object* x_615; 
lean_free_object(x_27);
lean_dec(x_11);
lean_dec(x_10);
x_614 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_615 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_614, x_1, x_2, x_417, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_1);
return x_615;
}
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; uint8_t x_625; uint8_t x_626; lean_object* x_627; lean_object* x_628; 
x_616 = lean_ctor_get(x_27, 1);
lean_inc(x_616);
lean_dec(x_27);
x_617 = lean_ctor_get(x_3, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_3, 1);
lean_inc(x_618);
x_619 = lean_ctor_get(x_3, 2);
lean_inc(x_619);
x_620 = lean_ctor_get(x_3, 3);
lean_inc(x_620);
x_621 = lean_ctor_get(x_3, 4);
lean_inc(x_621);
x_622 = lean_ctor_get(x_3, 5);
lean_inc(x_622);
x_623 = lean_ctor_get(x_3, 6);
lean_inc(x_623);
x_624 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_625 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_626 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_627 = x_3;
} else {
 lean_dec_ref(x_3);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(0, 8, 3);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_617);
lean_ctor_set(x_628, 1, x_618);
lean_ctor_set(x_628, 2, x_619);
lean_ctor_set(x_628, 3, x_620);
lean_ctor_set(x_628, 4, x_621);
lean_ctor_set(x_628, 5, x_622);
lean_ctor_set(x_628, 6, x_623);
lean_ctor_set(x_628, 7, x_24);
lean_ctor_set_uint8(x_628, sizeof(void*)*8, x_624);
lean_ctor_set_uint8(x_628, sizeof(void*)*8 + 1, x_625);
lean_ctor_set_uint8(x_628, sizeof(void*)*8 + 2, x_626);
if (x_20 == 0)
{
lean_object* x_629; uint8_t x_630; 
x_629 = l___private_Lean_Elab_Match_28__collect___main___closed__2;
x_630 = lean_name_eq(x_10, x_629);
if (x_630 == 0)
{
lean_object* x_631; uint8_t x_632; 
x_631 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_632 = lean_name_eq(x_10, x_631);
if (x_632 == 0)
{
lean_object* x_633; uint8_t x_634; 
x_633 = l_Lean_mkHole___closed__2;
x_634 = lean_name_eq(x_10, x_633);
if (x_634 == 0)
{
lean_object* x_635; uint8_t x_636; 
x_635 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_636 = lean_name_eq(x_10, x_635);
if (x_636 == 0)
{
lean_object* x_637; uint8_t x_638; 
lean_dec(x_11);
x_637 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
x_638 = lean_name_eq(x_10, x_637);
if (x_638 == 0)
{
lean_object* x_639; uint8_t x_640; 
x_639 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
x_640 = lean_name_eq(x_10, x_639);
if (x_640 == 0)
{
lean_object* x_641; uint8_t x_642; 
x_641 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_642 = lean_name_eq(x_10, x_641);
if (x_642 == 0)
{
lean_object* x_643; uint8_t x_644; 
x_643 = l_Lean_strLitKind;
x_644 = lean_name_eq(x_10, x_643);
if (x_644 == 0)
{
lean_object* x_645; uint8_t x_646; 
x_645 = l_Lean_numLitKind;
x_646 = lean_name_eq(x_10, x_645);
if (x_646 == 0)
{
lean_object* x_647; uint8_t x_648; 
x_647 = l_Lean_charLitKind;
x_648 = lean_name_eq(x_10, x_647);
if (x_648 == 0)
{
lean_object* x_649; uint8_t x_650; 
x_649 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_650 = lean_name_eq(x_10, x_649);
if (x_650 == 0)
{
lean_object* x_651; uint8_t x_652; 
lean_dec(x_1);
x_651 = l_Lean_choiceKind;
x_652 = lean_name_eq(x_10, x_651);
lean_dec(x_10);
if (x_652 == 0)
{
lean_object* x_653; 
x_653 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_653;
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = l___private_Lean_Elab_Match_28__collect___main___closed__5;
x_655 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_654, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_655;
}
}
else
{
lean_object* x_656; 
lean_dec(x_10);
lean_dec(x_2);
x_656 = l___private_Lean_Elab_Match_27__quotedNameToPattern(x_1, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_656;
}
}
else
{
lean_object* x_657; 
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_1);
lean_ctor_set(x_657, 1, x_616);
return x_657;
}
}
else
{
lean_object* x_658; 
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_658, 0, x_1);
lean_ctor_set(x_658, 1, x_616);
return x_658;
}
}
else
{
lean_object* x_659; 
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_1);
lean_ctor_set(x_659, 1, x_616);
return x_659;
}
}
else
{
lean_object* x_660; 
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_1);
lean_ctor_set(x_660, 1, x_616);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_10);
x_661 = lean_unsigned_to_nat(0u);
x_662 = l_Lean_Syntax_getArg(x_1, x_661);
lean_inc(x_628);
lean_inc(x_662);
x_663 = l___private_Lean_Elab_Match_24__processVar(x_662, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
lean_dec(x_663);
x_665 = lean_unsigned_to_nat(2u);
x_666 = l_Lean_Syntax_getArg(x_1, x_665);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_667 = x_1;
} else {
 lean_dec_ref(x_1);
 x_667 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_628);
x_668 = l___private_Lean_Elab_Match_28__collect___main(x_666, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_664);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
x_671 = l_Lean_Elab_Term_getCurrMacroScope(x_628, x_4, x_5, x_6, x_7, x_8, x_670);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_628);
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec(x_671);
x_674 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_673);
lean_dec(x_8);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_677 = x_674;
} else {
 lean_dec_ref(x_674);
 x_677 = lean_box(0);
}
x_678 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_679 = l_Lean_addMacroScope(x_675, x_678, x_672);
x_680 = l_Lean_SourceInfo_inhabited___closed__1;
x_681 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_682 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
x_683 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_683, 0, x_680);
lean_ctor_set(x_683, 1, x_681);
lean_ctor_set(x_683, 2, x_679);
lean_ctor_set(x_683, 3, x_682);
x_684 = l_Array_empty___closed__1;
x_685 = lean_array_push(x_684, x_683);
x_686 = lean_array_push(x_684, x_662);
x_687 = lean_array_push(x_686, x_669);
x_688 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_667)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_667;
}
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_687);
x_690 = lean_array_push(x_685, x_689);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_12);
lean_ctor_set(x_691, 1, x_690);
if (lean_is_scalar(x_677)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_677;
}
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_676);
return x_692;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_667);
lean_dec(x_662);
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_693 = lean_ctor_get(x_668, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_668, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_695 = x_668;
} else {
 lean_dec_ref(x_668);
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
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_662);
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_697 = lean_ctor_get(x_663, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_663, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_699 = x_663;
} else {
 lean_dec_ref(x_663);
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
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_10);
x_701 = lean_unsigned_to_nat(0u);
x_702 = l_Lean_Syntax_getArg(x_1, x_701);
lean_dec(x_1);
x_703 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_704 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_703, x_702, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
return x_704;
}
}
else
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_705 = l_Lean_Syntax_inhabited;
x_706 = lean_array_get(x_705, x_11, x_25);
x_707 = l_Lean_Syntax_isNone(x_706);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; uint8_t x_712; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_708 = x_1;
} else {
 lean_dec_ref(x_1);
 x_708 = lean_box(0);
}
x_709 = lean_unsigned_to_nat(0u);
x_710 = l_Lean_Syntax_getArg(x_706, x_709);
x_711 = l_Lean_Syntax_getArg(x_706, x_25);
x_712 = l_Lean_Syntax_isNone(x_711);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; uint8_t x_715; 
x_713 = l_Lean_Syntax_getArg(x_711, x_709);
x_714 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_inc(x_713);
x_715 = l_Lean_Syntax_isOfKind(x_713, x_714);
if (x_715 == 0)
{
lean_object* x_716; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_628);
lean_inc(x_2);
x_716 = l___private_Lean_Elab_Match_28__collect___main(x_710, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
x_719 = l_Lean_Syntax_setArg(x_706, x_709, x_717);
x_720 = l_Lean_Syntax_getArg(x_713, x_25);
x_721 = l_Lean_Syntax_getArgs(x_720);
lean_dec(x_720);
x_722 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_723 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_721, x_722, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_718);
lean_dec(x_721);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_726 = x_723;
} else {
 lean_dec_ref(x_723);
 x_726 = lean_box(0);
}
x_727 = l_Lean_nullKind;
if (lean_is_scalar(x_708)) {
 x_728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_728 = x_708;
}
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_724);
x_729 = l_Lean_Syntax_setArg(x_713, x_25, x_728);
x_730 = l_Lean_Syntax_setArg(x_711, x_709, x_729);
x_731 = l_Lean_Syntax_setArg(x_719, x_25, x_730);
x_732 = lean_array_set(x_11, x_25, x_731);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_10);
lean_ctor_set(x_733, 1, x_732);
if (lean_is_scalar(x_726)) {
 x_734 = lean_alloc_ctor(0, 2, 0);
} else {
 x_734 = x_726;
}
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_725);
return x_734;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_719);
lean_dec(x_713);
lean_dec(x_711);
lean_dec(x_708);
lean_dec(x_11);
lean_dec(x_10);
x_735 = lean_ctor_get(x_723, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_723, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_737 = x_723;
} else {
 lean_dec_ref(x_723);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_713);
lean_dec(x_711);
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_739 = lean_ctor_get(x_716, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_716, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_741 = x_716;
} else {
 lean_dec_ref(x_716);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
else
{
lean_object* x_743; 
lean_dec(x_713);
lean_dec(x_711);
x_743 = l___private_Lean_Elab_Match_28__collect___main(x_710, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_746 = x_743;
} else {
 lean_dec_ref(x_743);
 x_746 = lean_box(0);
}
x_747 = l_Lean_Syntax_setArg(x_706, x_709, x_744);
x_748 = lean_array_set(x_11, x_25, x_747);
if (lean_is_scalar(x_708)) {
 x_749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_749 = x_708;
}
lean_ctor_set(x_749, 0, x_10);
lean_ctor_set(x_749, 1, x_748);
if (lean_is_scalar(x_746)) {
 x_750 = lean_alloc_ctor(0, 2, 0);
} else {
 x_750 = x_746;
}
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_745);
return x_750;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_11);
lean_dec(x_10);
x_751 = lean_ctor_get(x_743, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_743, 1);
lean_inc(x_752);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_753 = x_743;
} else {
 lean_dec_ref(x_743);
 x_753 = lean_box(0);
}
if (lean_is_scalar(x_753)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_753;
}
lean_ctor_set(x_754, 0, x_751);
lean_ctor_set(x_754, 1, x_752);
return x_754;
}
}
}
else
{
lean_object* x_755; 
lean_dec(x_711);
x_755 = l___private_Lean_Elab_Match_28__collect___main(x_710, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_758 = x_755;
} else {
 lean_dec_ref(x_755);
 x_758 = lean_box(0);
}
x_759 = l_Lean_Syntax_setArg(x_706, x_709, x_756);
x_760 = lean_array_set(x_11, x_25, x_759);
if (lean_is_scalar(x_708)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_708;
}
lean_ctor_set(x_761, 0, x_10);
lean_ctor_set(x_761, 1, x_760);
if (lean_is_scalar(x_758)) {
 x_762 = lean_alloc_ctor(0, 2, 0);
} else {
 x_762 = x_758;
}
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_757);
return x_762;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_11);
lean_dec(x_10);
x_763 = lean_ctor_get(x_755, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_755, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_765 = x_755;
} else {
 lean_dec_ref(x_755);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_764);
return x_766;
}
}
}
else
{
lean_object* x_767; 
lean_dec(x_706);
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_1);
lean_ctor_set(x_767, 1, x_616);
return x_767;
}
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_628);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_768 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_616);
lean_dec(x_8);
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = lean_st_ref_take(x_2, x_770);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_774 = lean_ctor_get(x_772, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_772, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_776 = x_772;
} else {
 lean_dec_ref(x_772);
 x_776 = lean_box(0);
}
x_777 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_769);
x_778 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_778, 0, x_777);
x_779 = lean_array_push(x_775, x_778);
if (lean_is_scalar(x_776)) {
 x_780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_780 = x_776;
}
lean_ctor_set(x_780, 0, x_774);
lean_ctor_set(x_780, 1, x_779);
x_781 = lean_st_ref_set(x_2, x_780, x_773);
lean_dec(x_2);
x_782 = lean_ctor_get(x_781, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_783 = x_781;
} else {
 lean_dec_ref(x_781);
 x_783 = lean_box(0);
}
if (lean_is_scalar(x_783)) {
 x_784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_784 = x_783;
}
lean_ctor_set(x_784, 0, x_769);
lean_ctor_set(x_784, 1, x_782);
return x_784;
}
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_785 = x_1;
} else {
 lean_dec_ref(x_1);
 x_785 = lean_box(0);
}
x_786 = l_Lean_Syntax_inhabited;
x_787 = lean_array_get(x_786, x_11, x_25);
x_788 = l_Lean_Syntax_isNone(x_787);
if (x_788 == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_785);
lean_dec(x_11);
lean_dec(x_10);
x_789 = l___private_Lean_Elab_Match_28__collect___main___closed__14;
x_790 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_787, x_789, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_787);
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_793 = x_790;
} else {
 lean_dec_ref(x_790);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_787);
x_795 = lean_unsigned_to_nat(2u);
x_796 = lean_array_get(x_786, x_11, x_795);
x_797 = l_Lean_Syntax_getArgs(x_796);
lean_dec(x_796);
x_798 = l___private_Lean_Elab_Match_28__collect___main___closed__15;
x_799 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_797, x_798, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_797);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
x_803 = l_Lean_nullKind;
if (lean_is_scalar(x_785)) {
 x_804 = lean_alloc_ctor(1, 2, 0);
} else {
 x_804 = x_785;
}
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_800);
x_805 = lean_array_set(x_11, x_795, x_804);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_10);
lean_ctor_set(x_806, 1, x_805);
if (lean_is_scalar(x_802)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_802;
}
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_801);
return x_807;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_785);
lean_dec(x_11);
lean_dec(x_10);
x_808 = lean_ctor_get(x_799, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_799, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_810 = x_799;
} else {
 lean_dec_ref(x_799);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(1, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_808);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
}
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_812 = x_1;
} else {
 lean_dec_ref(x_1);
 x_812 = lean_box(0);
}
x_813 = l_Lean_Syntax_inhabited;
x_814 = lean_array_get(x_813, x_11, x_25);
x_815 = l_Lean_Syntax_getArgs(x_814);
lean_dec(x_814);
x_816 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_817 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_815, x_816, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_815);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
x_821 = l_Lean_nullKind;
if (lean_is_scalar(x_812)) {
 x_822 = lean_alloc_ctor(1, 2, 0);
} else {
 x_822 = x_812;
}
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_818);
x_823 = lean_array_set(x_11, x_25, x_822);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_10);
lean_ctor_set(x_824, 1, x_823);
if (lean_is_scalar(x_820)) {
 x_825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_825 = x_820;
}
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_819);
return x_825;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_812);
lean_dec(x_11);
lean_dec(x_10);
x_826 = lean_ctor_get(x_817, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_817, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_828 = x_817;
} else {
 lean_dec_ref(x_817);
 x_828 = lean_box(0);
}
if (lean_is_scalar(x_828)) {
 x_829 = lean_alloc_ctor(1, 2, 0);
} else {
 x_829 = x_828;
}
lean_ctor_set(x_829, 0, x_826);
lean_ctor_set(x_829, 1, x_827);
return x_829;
}
}
}
else
{
lean_object* x_830; lean_object* x_831; 
lean_dec(x_11);
lean_dec(x_10);
x_830 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_831 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_830, x_1, x_2, x_628, x_4, x_5, x_6, x_7, x_8, x_616);
lean_dec(x_1);
return x_831;
}
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; uint8_t x_851; uint8_t x_852; lean_object* x_853; lean_object* x_854; 
x_832 = lean_ctor_get(x_21, 0);
x_833 = lean_ctor_get(x_21, 1);
x_834 = lean_ctor_get(x_21, 2);
x_835 = lean_ctor_get(x_21, 3);
x_836 = lean_ctor_get(x_21, 4);
lean_inc(x_836);
lean_inc(x_835);
lean_inc(x_834);
lean_inc(x_833);
lean_inc(x_832);
lean_dec(x_21);
x_837 = lean_unsigned_to_nat(1u);
x_838 = lean_nat_add(x_835, x_837);
x_839 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_839, 0, x_832);
lean_ctor_set(x_839, 1, x_833);
lean_ctor_set(x_839, 2, x_834);
lean_ctor_set(x_839, 3, x_838);
lean_ctor_set(x_839, 4, x_836);
x_840 = lean_st_ref_set(x_4, x_839, x_22);
x_841 = lean_ctor_get(x_840, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_842 = x_840;
} else {
 lean_dec_ref(x_840);
 x_842 = lean_box(0);
}
x_843 = lean_ctor_get(x_3, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_3, 1);
lean_inc(x_844);
x_845 = lean_ctor_get(x_3, 2);
lean_inc(x_845);
x_846 = lean_ctor_get(x_3, 3);
lean_inc(x_846);
x_847 = lean_ctor_get(x_3, 4);
lean_inc(x_847);
x_848 = lean_ctor_get(x_3, 5);
lean_inc(x_848);
x_849 = lean_ctor_get(x_3, 6);
lean_inc(x_849);
x_850 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_851 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_852 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_853 = x_3;
} else {
 lean_dec_ref(x_3);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(0, 8, 3);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_843);
lean_ctor_set(x_854, 1, x_844);
lean_ctor_set(x_854, 2, x_845);
lean_ctor_set(x_854, 3, x_846);
lean_ctor_set(x_854, 4, x_847);
lean_ctor_set(x_854, 5, x_848);
lean_ctor_set(x_854, 6, x_849);
lean_ctor_set(x_854, 7, x_835);
lean_ctor_set_uint8(x_854, sizeof(void*)*8, x_850);
lean_ctor_set_uint8(x_854, sizeof(void*)*8 + 1, x_851);
lean_ctor_set_uint8(x_854, sizeof(void*)*8 + 2, x_852);
if (x_20 == 0)
{
lean_object* x_855; uint8_t x_856; 
x_855 = l___private_Lean_Elab_Match_28__collect___main___closed__2;
x_856 = lean_name_eq(x_10, x_855);
if (x_856 == 0)
{
lean_object* x_857; uint8_t x_858; 
x_857 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_858 = lean_name_eq(x_10, x_857);
if (x_858 == 0)
{
lean_object* x_859; uint8_t x_860; 
x_859 = l_Lean_mkHole___closed__2;
x_860 = lean_name_eq(x_10, x_859);
if (x_860 == 0)
{
lean_object* x_861; uint8_t x_862; 
x_861 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_862 = lean_name_eq(x_10, x_861);
if (x_862 == 0)
{
lean_object* x_863; uint8_t x_864; 
lean_dec(x_11);
x_863 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
x_864 = lean_name_eq(x_10, x_863);
if (x_864 == 0)
{
lean_object* x_865; uint8_t x_866; 
x_865 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
x_866 = lean_name_eq(x_10, x_865);
if (x_866 == 0)
{
lean_object* x_867; uint8_t x_868; 
x_867 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_868 = lean_name_eq(x_10, x_867);
if (x_868 == 0)
{
lean_object* x_869; uint8_t x_870; 
x_869 = l_Lean_strLitKind;
x_870 = lean_name_eq(x_10, x_869);
if (x_870 == 0)
{
lean_object* x_871; uint8_t x_872; 
x_871 = l_Lean_numLitKind;
x_872 = lean_name_eq(x_10, x_871);
if (x_872 == 0)
{
lean_object* x_873; uint8_t x_874; 
x_873 = l_Lean_charLitKind;
x_874 = lean_name_eq(x_10, x_873);
if (x_874 == 0)
{
lean_object* x_875; uint8_t x_876; 
lean_dec(x_842);
x_875 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_876 = lean_name_eq(x_10, x_875);
if (x_876 == 0)
{
lean_object* x_877; uint8_t x_878; 
lean_dec(x_1);
x_877 = l_Lean_choiceKind;
x_878 = lean_name_eq(x_10, x_877);
lean_dec(x_10);
if (x_878 == 0)
{
lean_object* x_879; 
x_879 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_879;
}
else
{
lean_object* x_880; lean_object* x_881; 
x_880 = l___private_Lean_Elab_Match_28__collect___main___closed__5;
x_881 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_880, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_881;
}
}
else
{
lean_object* x_882; 
lean_dec(x_10);
lean_dec(x_2);
x_882 = l___private_Lean_Elab_Match_27__quotedNameToPattern(x_1, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_882;
}
}
else
{
lean_object* x_883; 
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_842)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_842;
}
lean_ctor_set(x_883, 0, x_1);
lean_ctor_set(x_883, 1, x_841);
return x_883;
}
}
else
{
lean_object* x_884; 
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_842)) {
 x_884 = lean_alloc_ctor(0, 2, 0);
} else {
 x_884 = x_842;
}
lean_ctor_set(x_884, 0, x_1);
lean_ctor_set(x_884, 1, x_841);
return x_884;
}
}
else
{
lean_object* x_885; 
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_842)) {
 x_885 = lean_alloc_ctor(0, 2, 0);
} else {
 x_885 = x_842;
}
lean_ctor_set(x_885, 0, x_1);
lean_ctor_set(x_885, 1, x_841);
return x_885;
}
}
else
{
lean_object* x_886; 
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_842)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_842;
}
lean_ctor_set(x_886, 0, x_1);
lean_ctor_set(x_886, 1, x_841);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec(x_842);
lean_dec(x_10);
x_887 = lean_unsigned_to_nat(0u);
x_888 = l_Lean_Syntax_getArg(x_1, x_887);
lean_inc(x_854);
lean_inc(x_888);
x_889 = l___private_Lean_Elab_Match_24__processVar(x_888, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_890 = lean_ctor_get(x_889, 1);
lean_inc(x_890);
lean_dec(x_889);
x_891 = lean_unsigned_to_nat(2u);
x_892 = l_Lean_Syntax_getArg(x_1, x_891);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_893 = x_1;
} else {
 lean_dec_ref(x_1);
 x_893 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_854);
x_894 = l___private_Lean_Elab_Match_28__collect___main(x_892, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_890);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_897 = l_Lean_Elab_Term_getCurrMacroScope(x_854, x_4, x_5, x_6, x_7, x_8, x_896);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_854);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
lean_dec(x_897);
x_900 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_899);
lean_dec(x_8);
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_900, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_900)) {
 lean_ctor_release(x_900, 0);
 lean_ctor_release(x_900, 1);
 x_903 = x_900;
} else {
 lean_dec_ref(x_900);
 x_903 = lean_box(0);
}
x_904 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_905 = l_Lean_addMacroScope(x_901, x_904, x_898);
x_906 = l_Lean_SourceInfo_inhabited___closed__1;
x_907 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_908 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
x_909 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_907);
lean_ctor_set(x_909, 2, x_905);
lean_ctor_set(x_909, 3, x_908);
x_910 = l_Array_empty___closed__1;
x_911 = lean_array_push(x_910, x_909);
x_912 = lean_array_push(x_910, x_888);
x_913 = lean_array_push(x_912, x_895);
x_914 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_893)) {
 x_915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_915 = x_893;
}
lean_ctor_set(x_915, 0, x_914);
lean_ctor_set(x_915, 1, x_913);
x_916 = lean_array_push(x_911, x_915);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_12);
lean_ctor_set(x_917, 1, x_916);
if (lean_is_scalar(x_903)) {
 x_918 = lean_alloc_ctor(0, 2, 0);
} else {
 x_918 = x_903;
}
lean_ctor_set(x_918, 0, x_917);
lean_ctor_set(x_918, 1, x_902);
return x_918;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_893);
lean_dec(x_888);
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_919 = lean_ctor_get(x_894, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_894, 1);
lean_inc(x_920);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_921 = x_894;
} else {
 lean_dec_ref(x_894);
 x_921 = lean_box(0);
}
if (lean_is_scalar(x_921)) {
 x_922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_922 = x_921;
}
lean_ctor_set(x_922, 0, x_919);
lean_ctor_set(x_922, 1, x_920);
return x_922;
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
lean_dec(x_888);
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_923 = lean_ctor_get(x_889, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_889, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_925 = x_889;
} else {
 lean_dec_ref(x_889);
 x_925 = lean_box(0);
}
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(1, 2, 0);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_923);
lean_ctor_set(x_926, 1, x_924);
return x_926;
}
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_842);
lean_dec(x_10);
x_927 = lean_unsigned_to_nat(0u);
x_928 = l_Lean_Syntax_getArg(x_1, x_927);
lean_dec(x_1);
x_929 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_930 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_929, x_928, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
return x_930;
}
}
else
{
lean_object* x_931; lean_object* x_932; uint8_t x_933; 
x_931 = l_Lean_Syntax_inhabited;
x_932 = lean_array_get(x_931, x_11, x_837);
x_933 = l_Lean_Syntax_isNone(x_932);
if (x_933 == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; uint8_t x_938; 
lean_dec(x_842);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_934 = x_1;
} else {
 lean_dec_ref(x_1);
 x_934 = lean_box(0);
}
x_935 = lean_unsigned_to_nat(0u);
x_936 = l_Lean_Syntax_getArg(x_932, x_935);
x_937 = l_Lean_Syntax_getArg(x_932, x_837);
x_938 = l_Lean_Syntax_isNone(x_937);
if (x_938 == 0)
{
lean_object* x_939; lean_object* x_940; uint8_t x_941; 
x_939 = l_Lean_Syntax_getArg(x_937, x_935);
x_940 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_inc(x_939);
x_941 = l_Lean_Syntax_isOfKind(x_939, x_940);
if (x_941 == 0)
{
lean_object* x_942; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_854);
lean_inc(x_2);
x_942 = l___private_Lean_Elab_Match_28__collect___main(x_936, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
lean_dec(x_942);
x_945 = l_Lean_Syntax_setArg(x_932, x_935, x_943);
x_946 = l_Lean_Syntax_getArg(x_939, x_837);
x_947 = l_Lean_Syntax_getArgs(x_946);
lean_dec(x_946);
x_948 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_949 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_947, x_948, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_944);
lean_dec(x_947);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_952 = x_949;
} else {
 lean_dec_ref(x_949);
 x_952 = lean_box(0);
}
x_953 = l_Lean_nullKind;
if (lean_is_scalar(x_934)) {
 x_954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_954 = x_934;
}
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_950);
x_955 = l_Lean_Syntax_setArg(x_939, x_837, x_954);
x_956 = l_Lean_Syntax_setArg(x_937, x_935, x_955);
x_957 = l_Lean_Syntax_setArg(x_945, x_837, x_956);
x_958 = lean_array_set(x_11, x_837, x_957);
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_10);
lean_ctor_set(x_959, 1, x_958);
if (lean_is_scalar(x_952)) {
 x_960 = lean_alloc_ctor(0, 2, 0);
} else {
 x_960 = x_952;
}
lean_ctor_set(x_960, 0, x_959);
lean_ctor_set(x_960, 1, x_951);
return x_960;
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
lean_dec(x_945);
lean_dec(x_939);
lean_dec(x_937);
lean_dec(x_934);
lean_dec(x_11);
lean_dec(x_10);
x_961 = lean_ctor_get(x_949, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_949, 1);
lean_inc(x_962);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_963 = x_949;
} else {
 lean_dec_ref(x_949);
 x_963 = lean_box(0);
}
if (lean_is_scalar(x_963)) {
 x_964 = lean_alloc_ctor(1, 2, 0);
} else {
 x_964 = x_963;
}
lean_ctor_set(x_964, 0, x_961);
lean_ctor_set(x_964, 1, x_962);
return x_964;
}
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_939);
lean_dec(x_937);
lean_dec(x_934);
lean_dec(x_932);
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_965 = lean_ctor_get(x_942, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_942, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_967 = x_942;
} else {
 lean_dec_ref(x_942);
 x_967 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_968 = x_967;
}
lean_ctor_set(x_968, 0, x_965);
lean_ctor_set(x_968, 1, x_966);
return x_968;
}
}
else
{
lean_object* x_969; 
lean_dec(x_939);
lean_dec(x_937);
x_969 = l___private_Lean_Elab_Match_28__collect___main(x_936, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_972 = x_969;
} else {
 lean_dec_ref(x_969);
 x_972 = lean_box(0);
}
x_973 = l_Lean_Syntax_setArg(x_932, x_935, x_970);
x_974 = lean_array_set(x_11, x_837, x_973);
if (lean_is_scalar(x_934)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_934;
}
lean_ctor_set(x_975, 0, x_10);
lean_ctor_set(x_975, 1, x_974);
if (lean_is_scalar(x_972)) {
 x_976 = lean_alloc_ctor(0, 2, 0);
} else {
 x_976 = x_972;
}
lean_ctor_set(x_976, 0, x_975);
lean_ctor_set(x_976, 1, x_971);
return x_976;
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_934);
lean_dec(x_932);
lean_dec(x_11);
lean_dec(x_10);
x_977 = lean_ctor_get(x_969, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_969, 1);
lean_inc(x_978);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_979 = x_969;
} else {
 lean_dec_ref(x_969);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(1, 2, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_977);
lean_ctor_set(x_980, 1, x_978);
return x_980;
}
}
}
else
{
lean_object* x_981; 
lean_dec(x_937);
x_981 = l___private_Lean_Elab_Match_28__collect___main(x_936, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_984 = x_981;
} else {
 lean_dec_ref(x_981);
 x_984 = lean_box(0);
}
x_985 = l_Lean_Syntax_setArg(x_932, x_935, x_982);
x_986 = lean_array_set(x_11, x_837, x_985);
if (lean_is_scalar(x_934)) {
 x_987 = lean_alloc_ctor(1, 2, 0);
} else {
 x_987 = x_934;
}
lean_ctor_set(x_987, 0, x_10);
lean_ctor_set(x_987, 1, x_986);
if (lean_is_scalar(x_984)) {
 x_988 = lean_alloc_ctor(0, 2, 0);
} else {
 x_988 = x_984;
}
lean_ctor_set(x_988, 0, x_987);
lean_ctor_set(x_988, 1, x_983);
return x_988;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec(x_934);
lean_dec(x_932);
lean_dec(x_11);
lean_dec(x_10);
x_989 = lean_ctor_get(x_981, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_981, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_991 = x_981;
} else {
 lean_dec_ref(x_981);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_989);
lean_ctor_set(x_992, 1, x_990);
return x_992;
}
}
}
else
{
lean_object* x_993; 
lean_dec(x_932);
lean_dec(x_854);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_842)) {
 x_993 = lean_alloc_ctor(0, 2, 0);
} else {
 x_993 = x_842;
}
lean_ctor_set(x_993, 0, x_1);
lean_ctor_set(x_993, 1, x_841);
return x_993;
}
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_854);
lean_dec(x_842);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_994 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_841);
lean_dec(x_8);
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec(x_994);
x_997 = lean_st_ref_take(x_2, x_996);
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
lean_dec(x_997);
x_1000 = lean_ctor_get(x_998, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_998, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1002 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1002 = lean_box(0);
}
x_1003 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_995);
x_1004 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1004, 0, x_1003);
x_1005 = lean_array_push(x_1001, x_1004);
if (lean_is_scalar(x_1002)) {
 x_1006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1006 = x_1002;
}
lean_ctor_set(x_1006, 0, x_1000);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = lean_st_ref_set(x_2, x_1006, x_999);
lean_dec(x_2);
x_1008 = lean_ctor_get(x_1007, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1009 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1009 = lean_box(0);
}
if (lean_is_scalar(x_1009)) {
 x_1010 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1010 = x_1009;
}
lean_ctor_set(x_1010, 0, x_995);
lean_ctor_set(x_1010, 1, x_1008);
return x_1010;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
lean_dec(x_842);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1011 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1011 = lean_box(0);
}
x_1012 = l_Lean_Syntax_inhabited;
x_1013 = lean_array_get(x_1012, x_11, x_837);
x_1014 = l_Lean_Syntax_isNone(x_1013);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_dec(x_1011);
lean_dec(x_11);
lean_dec(x_10);
x_1015 = l___private_Lean_Elab_Match_28__collect___main___closed__14;
x_1016 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_1013, x_1015, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1013);
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1019 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1019 = lean_box(0);
}
if (lean_is_scalar(x_1019)) {
 x_1020 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1020 = x_1019;
}
lean_ctor_set(x_1020, 0, x_1017);
lean_ctor_set(x_1020, 1, x_1018);
return x_1020;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_1013);
x_1021 = lean_unsigned_to_nat(2u);
x_1022 = lean_array_get(x_1012, x_11, x_1021);
x_1023 = l_Lean_Syntax_getArgs(x_1022);
lean_dec(x_1022);
x_1024 = l___private_Lean_Elab_Match_28__collect___main___closed__15;
x_1025 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_1023, x_1024, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_1023);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 lean_ctor_release(x_1025, 1);
 x_1028 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1028 = lean_box(0);
}
x_1029 = l_Lean_nullKind;
if (lean_is_scalar(x_1011)) {
 x_1030 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1030 = x_1011;
}
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_1026);
x_1031 = lean_array_set(x_11, x_1021, x_1030);
x_1032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1032, 0, x_10);
lean_ctor_set(x_1032, 1, x_1031);
if (lean_is_scalar(x_1028)) {
 x_1033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1033 = x_1028;
}
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_1027);
return x_1033;
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_1011);
lean_dec(x_11);
lean_dec(x_10);
x_1034 = lean_ctor_get(x_1025, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1025, 1);
lean_inc(x_1035);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 lean_ctor_release(x_1025, 1);
 x_1036 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1036 = lean_box(0);
}
if (lean_is_scalar(x_1036)) {
 x_1037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1037 = x_1036;
}
lean_ctor_set(x_1037, 0, x_1034);
lean_ctor_set(x_1037, 1, x_1035);
return x_1037;
}
}
}
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_842);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1038 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1038 = lean_box(0);
}
x_1039 = l_Lean_Syntax_inhabited;
x_1040 = lean_array_get(x_1039, x_11, x_837);
x_1041 = l_Lean_Syntax_getArgs(x_1040);
lean_dec(x_1040);
x_1042 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1043 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_1041, x_1042, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_1041);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1043, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1046 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1046 = lean_box(0);
}
x_1047 = l_Lean_nullKind;
if (lean_is_scalar(x_1038)) {
 x_1048 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1048 = x_1038;
}
lean_ctor_set(x_1048, 0, x_1047);
lean_ctor_set(x_1048, 1, x_1044);
x_1049 = lean_array_set(x_11, x_837, x_1048);
x_1050 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1050, 0, x_10);
lean_ctor_set(x_1050, 1, x_1049);
if (lean_is_scalar(x_1046)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_1046;
}
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_1045);
return x_1051;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1038);
lean_dec(x_11);
lean_dec(x_10);
x_1052 = lean_ctor_get(x_1043, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1043, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1054 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
}
else
{
lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_842);
lean_dec(x_11);
lean_dec(x_10);
x_1056 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1057 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_1056, x_1, x_2, x_854, x_4, x_5, x_6, x_7, x_8, x_841);
lean_dec(x_1);
return x_1057;
}
}
}
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; uint8_t x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1065 = lean_ctor_get(x_7, 0);
x_1066 = lean_ctor_get(x_7, 1);
x_1067 = lean_ctor_get(x_7, 2);
x_1068 = lean_ctor_get(x_7, 3);
lean_inc(x_1068);
lean_inc(x_1067);
lean_inc(x_1066);
lean_inc(x_1065);
lean_dec(x_7);
x_1069 = l_Lean_replaceRef(x_1, x_1068);
x_1070 = l_Lean_replaceRef(x_1069, x_1068);
lean_dec(x_1069);
x_1071 = l_Lean_replaceRef(x_1070, x_1068);
lean_dec(x_1068);
lean_dec(x_1070);
x_1072 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1072, 0, x_1065);
lean_ctor_set(x_1072, 1, x_1066);
lean_ctor_set(x_1072, 2, x_1067);
lean_ctor_set(x_1072, 3, x_1071);
x_1073 = lean_st_ref_take(x_4, x_9);
if (x_13 == 0)
{
lean_object* x_1305; lean_object* x_1306; uint8_t x_1307; 
x_1305 = lean_ctor_get(x_1073, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1073, 1);
lean_inc(x_1306);
lean_dec(x_1073);
x_1307 = 0;
x_1074 = x_1307;
x_1075 = x_1305;
x_1076 = x_1306;
goto block_1304;
}
else
{
lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; 
x_1308 = lean_ctor_get(x_1073, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1073, 1);
lean_inc(x_1309);
lean_dec(x_1073);
x_1310 = 1;
x_1074 = x_1310;
x_1075 = x_1308;
x_1076 = x_1309;
goto block_1304;
}
block_1304:
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; uint8_t x_1097; uint8_t x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1077 = lean_ctor_get(x_1075, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1075, 1);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1075, 2);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1075, 3);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1075, 4);
lean_inc(x_1081);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 lean_ctor_release(x_1075, 1);
 lean_ctor_release(x_1075, 2);
 lean_ctor_release(x_1075, 3);
 lean_ctor_release(x_1075, 4);
 x_1082 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1082 = lean_box(0);
}
x_1083 = lean_unsigned_to_nat(1u);
x_1084 = lean_nat_add(x_1080, x_1083);
if (lean_is_scalar(x_1082)) {
 x_1085 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1085 = x_1082;
}
lean_ctor_set(x_1085, 0, x_1077);
lean_ctor_set(x_1085, 1, x_1078);
lean_ctor_set(x_1085, 2, x_1079);
lean_ctor_set(x_1085, 3, x_1084);
lean_ctor_set(x_1085, 4, x_1081);
x_1086 = lean_st_ref_set(x_4, x_1085, x_1076);
x_1087 = lean_ctor_get(x_1086, 1);
lean_inc(x_1087);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1088 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1088 = lean_box(0);
}
x_1089 = lean_ctor_get(x_3, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_3, 1);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_3, 2);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_3, 3);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_3, 4);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_3, 5);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_3, 6);
lean_inc(x_1095);
x_1096 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_1097 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_1098 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_1099 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1099 = lean_box(0);
}
if (lean_is_scalar(x_1099)) {
 x_1100 = lean_alloc_ctor(0, 8, 3);
} else {
 x_1100 = x_1099;
}
lean_ctor_set(x_1100, 0, x_1089);
lean_ctor_set(x_1100, 1, x_1090);
lean_ctor_set(x_1100, 2, x_1091);
lean_ctor_set(x_1100, 3, x_1092);
lean_ctor_set(x_1100, 4, x_1093);
lean_ctor_set(x_1100, 5, x_1094);
lean_ctor_set(x_1100, 6, x_1095);
lean_ctor_set(x_1100, 7, x_1080);
lean_ctor_set_uint8(x_1100, sizeof(void*)*8, x_1096);
lean_ctor_set_uint8(x_1100, sizeof(void*)*8 + 1, x_1097);
lean_ctor_set_uint8(x_1100, sizeof(void*)*8 + 2, x_1098);
if (x_1074 == 0)
{
lean_object* x_1101; uint8_t x_1102; 
x_1101 = l___private_Lean_Elab_Match_28__collect___main___closed__2;
x_1102 = lean_name_eq(x_10, x_1101);
if (x_1102 == 0)
{
lean_object* x_1103; uint8_t x_1104; 
x_1103 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_1104 = lean_name_eq(x_10, x_1103);
if (x_1104 == 0)
{
lean_object* x_1105; uint8_t x_1106; 
x_1105 = l_Lean_mkHole___closed__2;
x_1106 = lean_name_eq(x_10, x_1105);
if (x_1106 == 0)
{
lean_object* x_1107; uint8_t x_1108; 
x_1107 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_1108 = lean_name_eq(x_10, x_1107);
if (x_1108 == 0)
{
lean_object* x_1109; uint8_t x_1110; 
lean_dec(x_11);
x_1109 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
x_1110 = lean_name_eq(x_10, x_1109);
if (x_1110 == 0)
{
lean_object* x_1111; uint8_t x_1112; 
x_1111 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
x_1112 = lean_name_eq(x_10, x_1111);
if (x_1112 == 0)
{
lean_object* x_1113; uint8_t x_1114; 
x_1113 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_1114 = lean_name_eq(x_10, x_1113);
if (x_1114 == 0)
{
lean_object* x_1115; uint8_t x_1116; 
x_1115 = l_Lean_strLitKind;
x_1116 = lean_name_eq(x_10, x_1115);
if (x_1116 == 0)
{
lean_object* x_1117; uint8_t x_1118; 
x_1117 = l_Lean_numLitKind;
x_1118 = lean_name_eq(x_10, x_1117);
if (x_1118 == 0)
{
lean_object* x_1119; uint8_t x_1120; 
x_1119 = l_Lean_charLitKind;
x_1120 = lean_name_eq(x_10, x_1119);
if (x_1120 == 0)
{
lean_object* x_1121; uint8_t x_1122; 
lean_dec(x_1088);
x_1121 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__2;
x_1122 = lean_name_eq(x_10, x_1121);
if (x_1122 == 0)
{
lean_object* x_1123; uint8_t x_1124; 
lean_dec(x_1);
x_1123 = l_Lean_choiceKind;
x_1124 = lean_name_eq(x_10, x_1123);
lean_dec(x_10);
if (x_1124 == 0)
{
lean_object* x_1125; 
x_1125 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_8);
lean_dec(x_1072);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1125;
}
else
{
lean_object* x_1126; lean_object* x_1127; 
x_1126 = l___private_Lean_Elab_Match_28__collect___main___closed__5;
x_1127 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_1126, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_8);
lean_dec(x_1072);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1127;
}
}
else
{
lean_object* x_1128; 
lean_dec(x_10);
lean_dec(x_2);
x_1128 = l___private_Lean_Elab_Match_27__quotedNameToPattern(x_1, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_8);
lean_dec(x_1072);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_1128;
}
}
else
{
lean_object* x_1129; 
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1088)) {
 x_1129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1129 = x_1088;
}
lean_ctor_set(x_1129, 0, x_1);
lean_ctor_set(x_1129, 1, x_1087);
return x_1129;
}
}
else
{
lean_object* x_1130; 
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1088)) {
 x_1130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1130 = x_1088;
}
lean_ctor_set(x_1130, 0, x_1);
lean_ctor_set(x_1130, 1, x_1087);
return x_1130;
}
}
else
{
lean_object* x_1131; 
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1088)) {
 x_1131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1131 = x_1088;
}
lean_ctor_set(x_1131, 0, x_1);
lean_ctor_set(x_1131, 1, x_1087);
return x_1131;
}
}
else
{
lean_object* x_1132; 
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1088)) {
 x_1132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1132 = x_1088;
}
lean_ctor_set(x_1132, 0, x_1);
lean_ctor_set(x_1132, 1, x_1087);
return x_1132;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
lean_dec(x_1088);
lean_dec(x_10);
x_1133 = lean_unsigned_to_nat(0u);
x_1134 = l_Lean_Syntax_getArg(x_1, x_1133);
lean_inc(x_1100);
lean_inc(x_1134);
x_1135 = l___private_Lean_Elab_Match_24__processVar(x_1134, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1136 = lean_ctor_get(x_1135, 1);
lean_inc(x_1136);
lean_dec(x_1135);
x_1137 = lean_unsigned_to_nat(2u);
x_1138 = l_Lean_Syntax_getArg(x_1, x_1137);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1139 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1139 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_1072);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1100);
x_1140 = l___private_Lean_Elab_Match_28__collect___main(x_1138, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1136);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec(x_1140);
x_1143 = l_Lean_Elab_Term_getCurrMacroScope(x_1100, x_4, x_5, x_6, x_1072, x_8, x_1142);
lean_dec(x_1072);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1100);
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1143, 1);
lean_inc(x_1145);
lean_dec(x_1143);
x_1146 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1145);
lean_dec(x_8);
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1146, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1146)) {
 lean_ctor_release(x_1146, 0);
 lean_ctor_release(x_1146, 1);
 x_1149 = x_1146;
} else {
 lean_dec_ref(x_1146);
 x_1149 = lean_box(0);
}
x_1150 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_1151 = l_Lean_addMacroScope(x_1147, x_1150, x_1144);
x_1152 = l_Lean_SourceInfo_inhabited___closed__1;
x_1153 = l___private_Lean_Elab_Match_28__collect___main___closed__7;
x_1154 = l___private_Lean_Elab_Match_28__collect___main___closed__10;
x_1155 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
lean_ctor_set(x_1155, 2, x_1151);
lean_ctor_set(x_1155, 3, x_1154);
x_1156 = l_Array_empty___closed__1;
x_1157 = lean_array_push(x_1156, x_1155);
x_1158 = lean_array_push(x_1156, x_1134);
x_1159 = lean_array_push(x_1158, x_1141);
x_1160 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_1139)) {
 x_1161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1161 = x_1139;
}
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1159);
x_1162 = lean_array_push(x_1157, x_1161);
x_1163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1163, 0, x_12);
lean_ctor_set(x_1163, 1, x_1162);
if (lean_is_scalar(x_1149)) {
 x_1164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1164 = x_1149;
}
lean_ctor_set(x_1164, 0, x_1163);
lean_ctor_set(x_1164, 1, x_1148);
return x_1164;
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1139);
lean_dec(x_1134);
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1165 = lean_ctor_get(x_1140, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1140, 1);
lean_inc(x_1166);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1167 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1167 = lean_box(0);
}
if (lean_is_scalar(x_1167)) {
 x_1168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1168 = x_1167;
}
lean_ctor_set(x_1168, 0, x_1165);
lean_ctor_set(x_1168, 1, x_1166);
return x_1168;
}
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1134);
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1169 = lean_ctor_get(x_1135, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1135, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1135)) {
 lean_ctor_release(x_1135, 0);
 lean_ctor_release(x_1135, 1);
 x_1171 = x_1135;
} else {
 lean_dec_ref(x_1135);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1169);
lean_ctor_set(x_1172, 1, x_1170);
return x_1172;
}
}
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_1088);
lean_dec(x_10);
x_1173 = lean_unsigned_to_nat(0u);
x_1174 = l_Lean_Syntax_getArg(x_1, x_1173);
lean_dec(x_1);
x_1175 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1176 = l_Lean_Elab_Term_CollectPatternVars_processCtor(x_1175, x_1174, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
return x_1176;
}
}
else
{
lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; 
x_1177 = l_Lean_Syntax_inhabited;
x_1178 = lean_array_get(x_1177, x_11, x_1083);
x_1179 = l_Lean_Syntax_isNone(x_1178);
if (x_1179 == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; uint8_t x_1184; 
lean_dec(x_1088);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1180 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1180 = lean_box(0);
}
x_1181 = lean_unsigned_to_nat(0u);
x_1182 = l_Lean_Syntax_getArg(x_1178, x_1181);
x_1183 = l_Lean_Syntax_getArg(x_1178, x_1083);
x_1184 = l_Lean_Syntax_isNone(x_1183);
if (x_1184 == 0)
{
lean_object* x_1185; lean_object* x_1186; uint8_t x_1187; 
x_1185 = l_Lean_Syntax_getArg(x_1183, x_1181);
x_1186 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_inc(x_1185);
x_1187 = l_Lean_Syntax_isOfKind(x_1185, x_1186);
if (x_1187 == 0)
{
lean_object* x_1188; 
lean_inc(x_8);
lean_inc(x_1072);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1100);
lean_inc(x_2);
x_1188 = l___private_Lean_Elab_Match_28__collect___main(x_1182, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1189 = lean_ctor_get(x_1188, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1188, 1);
lean_inc(x_1190);
lean_dec(x_1188);
x_1191 = l_Lean_Syntax_setArg(x_1178, x_1181, x_1189);
x_1192 = l_Lean_Syntax_getArg(x_1185, x_1083);
x_1193 = l_Lean_Syntax_getArgs(x_1192);
lean_dec(x_1192);
x_1194 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1195 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_1193, x_1194, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1190);
lean_dec(x_1193);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
if (lean_is_exclusive(x_1195)) {
 lean_ctor_release(x_1195, 0);
 lean_ctor_release(x_1195, 1);
 x_1198 = x_1195;
} else {
 lean_dec_ref(x_1195);
 x_1198 = lean_box(0);
}
x_1199 = l_Lean_nullKind;
if (lean_is_scalar(x_1180)) {
 x_1200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1200 = x_1180;
}
lean_ctor_set(x_1200, 0, x_1199);
lean_ctor_set(x_1200, 1, x_1196);
x_1201 = l_Lean_Syntax_setArg(x_1185, x_1083, x_1200);
x_1202 = l_Lean_Syntax_setArg(x_1183, x_1181, x_1201);
x_1203 = l_Lean_Syntax_setArg(x_1191, x_1083, x_1202);
x_1204 = lean_array_set(x_11, x_1083, x_1203);
x_1205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1205, 0, x_10);
lean_ctor_set(x_1205, 1, x_1204);
if (lean_is_scalar(x_1198)) {
 x_1206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1206 = x_1198;
}
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_1197);
return x_1206;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
lean_dec(x_1191);
lean_dec(x_1185);
lean_dec(x_1183);
lean_dec(x_1180);
lean_dec(x_11);
lean_dec(x_10);
x_1207 = lean_ctor_get(x_1195, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1195, 1);
lean_inc(x_1208);
if (lean_is_exclusive(x_1195)) {
 lean_ctor_release(x_1195, 0);
 lean_ctor_release(x_1195, 1);
 x_1209 = x_1195;
} else {
 lean_dec_ref(x_1195);
 x_1209 = lean_box(0);
}
if (lean_is_scalar(x_1209)) {
 x_1210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1210 = x_1209;
}
lean_ctor_set(x_1210, 0, x_1207);
lean_ctor_set(x_1210, 1, x_1208);
return x_1210;
}
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
lean_dec(x_1185);
lean_dec(x_1183);
lean_dec(x_1180);
lean_dec(x_1178);
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1211 = lean_ctor_get(x_1188, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1188, 1);
lean_inc(x_1212);
if (lean_is_exclusive(x_1188)) {
 lean_ctor_release(x_1188, 0);
 lean_ctor_release(x_1188, 1);
 x_1213 = x_1188;
} else {
 lean_dec_ref(x_1188);
 x_1213 = lean_box(0);
}
if (lean_is_scalar(x_1213)) {
 x_1214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1214 = x_1213;
}
lean_ctor_set(x_1214, 0, x_1211);
lean_ctor_set(x_1214, 1, x_1212);
return x_1214;
}
}
else
{
lean_object* x_1215; 
lean_dec(x_1185);
lean_dec(x_1183);
x_1215 = l___private_Lean_Elab_Match_28__collect___main(x_1182, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
x_1216 = lean_ctor_get(x_1215, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1215, 1);
lean_inc(x_1217);
if (lean_is_exclusive(x_1215)) {
 lean_ctor_release(x_1215, 0);
 lean_ctor_release(x_1215, 1);
 x_1218 = x_1215;
} else {
 lean_dec_ref(x_1215);
 x_1218 = lean_box(0);
}
x_1219 = l_Lean_Syntax_setArg(x_1178, x_1181, x_1216);
x_1220 = lean_array_set(x_11, x_1083, x_1219);
if (lean_is_scalar(x_1180)) {
 x_1221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1221 = x_1180;
}
lean_ctor_set(x_1221, 0, x_10);
lean_ctor_set(x_1221, 1, x_1220);
if (lean_is_scalar(x_1218)) {
 x_1222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1222 = x_1218;
}
lean_ctor_set(x_1222, 0, x_1221);
lean_ctor_set(x_1222, 1, x_1217);
return x_1222;
}
else
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
lean_dec(x_1180);
lean_dec(x_1178);
lean_dec(x_11);
lean_dec(x_10);
x_1223 = lean_ctor_get(x_1215, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1215, 1);
lean_inc(x_1224);
if (lean_is_exclusive(x_1215)) {
 lean_ctor_release(x_1215, 0);
 lean_ctor_release(x_1215, 1);
 x_1225 = x_1215;
} else {
 lean_dec_ref(x_1215);
 x_1225 = lean_box(0);
}
if (lean_is_scalar(x_1225)) {
 x_1226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1226 = x_1225;
}
lean_ctor_set(x_1226, 0, x_1223);
lean_ctor_set(x_1226, 1, x_1224);
return x_1226;
}
}
}
else
{
lean_object* x_1227; 
lean_dec(x_1183);
x_1227 = l___private_Lean_Elab_Match_28__collect___main(x_1182, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
if (lean_obj_tag(x_1227) == 0)
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
x_1228 = lean_ctor_get(x_1227, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get(x_1227, 1);
lean_inc(x_1229);
if (lean_is_exclusive(x_1227)) {
 lean_ctor_release(x_1227, 0);
 lean_ctor_release(x_1227, 1);
 x_1230 = x_1227;
} else {
 lean_dec_ref(x_1227);
 x_1230 = lean_box(0);
}
x_1231 = l_Lean_Syntax_setArg(x_1178, x_1181, x_1228);
x_1232 = lean_array_set(x_11, x_1083, x_1231);
if (lean_is_scalar(x_1180)) {
 x_1233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1233 = x_1180;
}
lean_ctor_set(x_1233, 0, x_10);
lean_ctor_set(x_1233, 1, x_1232);
if (lean_is_scalar(x_1230)) {
 x_1234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1234 = x_1230;
}
lean_ctor_set(x_1234, 0, x_1233);
lean_ctor_set(x_1234, 1, x_1229);
return x_1234;
}
else
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
lean_dec(x_1180);
lean_dec(x_1178);
lean_dec(x_11);
lean_dec(x_10);
x_1235 = lean_ctor_get(x_1227, 0);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1227, 1);
lean_inc(x_1236);
if (lean_is_exclusive(x_1227)) {
 lean_ctor_release(x_1227, 0);
 lean_ctor_release(x_1227, 1);
 x_1237 = x_1227;
} else {
 lean_dec_ref(x_1227);
 x_1237 = lean_box(0);
}
if (lean_is_scalar(x_1237)) {
 x_1238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1238 = x_1237;
}
lean_ctor_set(x_1238, 0, x_1235);
lean_ctor_set(x_1238, 1, x_1236);
return x_1238;
}
}
}
else
{
lean_object* x_1239; 
lean_dec(x_1178);
lean_dec(x_1100);
lean_dec(x_1072);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1088)) {
 x_1239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1239 = x_1088;
}
lean_ctor_set(x_1239, 0, x_1);
lean_ctor_set(x_1239, 1, x_1087);
return x_1239;
}
}
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
lean_dec(x_1100);
lean_dec(x_1088);
lean_dec(x_1072);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1240 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_1087);
lean_dec(x_8);
x_1241 = lean_ctor_get(x_1240, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1240, 1);
lean_inc(x_1242);
lean_dec(x_1240);
x_1243 = lean_st_ref_take(x_2, x_1242);
x_1244 = lean_ctor_get(x_1243, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1243, 1);
lean_inc(x_1245);
lean_dec(x_1243);
x_1246 = lean_ctor_get(x_1244, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1244, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1244)) {
 lean_ctor_release(x_1244, 0);
 lean_ctor_release(x_1244, 1);
 x_1248 = x_1244;
} else {
 lean_dec_ref(x_1244);
 x_1248 = lean_box(0);
}
x_1249 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1241);
x_1250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1250, 0, x_1249);
x_1251 = lean_array_push(x_1247, x_1250);
if (lean_is_scalar(x_1248)) {
 x_1252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1252 = x_1248;
}
lean_ctor_set(x_1252, 0, x_1246);
lean_ctor_set(x_1252, 1, x_1251);
x_1253 = lean_st_ref_set(x_2, x_1252, x_1245);
lean_dec(x_2);
x_1254 = lean_ctor_get(x_1253, 1);
lean_inc(x_1254);
if (lean_is_exclusive(x_1253)) {
 lean_ctor_release(x_1253, 0);
 lean_ctor_release(x_1253, 1);
 x_1255 = x_1253;
} else {
 lean_dec_ref(x_1253);
 x_1255 = lean_box(0);
}
if (lean_is_scalar(x_1255)) {
 x_1256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1256 = x_1255;
}
lean_ctor_set(x_1256, 0, x_1241);
lean_ctor_set(x_1256, 1, x_1254);
return x_1256;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; 
lean_dec(x_1088);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1257 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1257 = lean_box(0);
}
x_1258 = l_Lean_Syntax_inhabited;
x_1259 = lean_array_get(x_1258, x_11, x_1083);
x_1260 = l_Lean_Syntax_isNone(x_1259);
if (x_1260 == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
lean_dec(x_1257);
lean_dec(x_11);
lean_dec(x_10);
x_1261 = l___private_Lean_Elab_Match_28__collect___main___closed__14;
x_1262 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_24__processVar___spec__1___rarg(x_1259, x_1261, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_8);
lean_dec(x_1072);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1259);
x_1263 = lean_ctor_get(x_1262, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1262, 1);
lean_inc(x_1264);
if (lean_is_exclusive(x_1262)) {
 lean_ctor_release(x_1262, 0);
 lean_ctor_release(x_1262, 1);
 x_1265 = x_1262;
} else {
 lean_dec_ref(x_1262);
 x_1265 = lean_box(0);
}
if (lean_is_scalar(x_1265)) {
 x_1266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1266 = x_1265;
}
lean_ctor_set(x_1266, 0, x_1263);
lean_ctor_set(x_1266, 1, x_1264);
return x_1266;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_1259);
x_1267 = lean_unsigned_to_nat(2u);
x_1268 = lean_array_get(x_1258, x_11, x_1267);
x_1269 = l_Lean_Syntax_getArgs(x_1268);
lean_dec(x_1268);
x_1270 = l___private_Lean_Elab_Match_28__collect___main___closed__15;
x_1271 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_1269, x_1270, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_1269);
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1272 = lean_ctor_get(x_1271, 0);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1271, 1);
lean_inc(x_1273);
if (lean_is_exclusive(x_1271)) {
 lean_ctor_release(x_1271, 0);
 lean_ctor_release(x_1271, 1);
 x_1274 = x_1271;
} else {
 lean_dec_ref(x_1271);
 x_1274 = lean_box(0);
}
x_1275 = l_Lean_nullKind;
if (lean_is_scalar(x_1257)) {
 x_1276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1276 = x_1257;
}
lean_ctor_set(x_1276, 0, x_1275);
lean_ctor_set(x_1276, 1, x_1272);
x_1277 = lean_array_set(x_11, x_1267, x_1276);
x_1278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1278, 0, x_10);
lean_ctor_set(x_1278, 1, x_1277);
if (lean_is_scalar(x_1274)) {
 x_1279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1279 = x_1274;
}
lean_ctor_set(x_1279, 0, x_1278);
lean_ctor_set(x_1279, 1, x_1273);
return x_1279;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1257);
lean_dec(x_11);
lean_dec(x_10);
x_1280 = lean_ctor_get(x_1271, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1271, 1);
lean_inc(x_1281);
if (lean_is_exclusive(x_1271)) {
 lean_ctor_release(x_1271, 0);
 lean_ctor_release(x_1271, 1);
 x_1282 = x_1271;
} else {
 lean_dec_ref(x_1271);
 x_1282 = lean_box(0);
}
if (lean_is_scalar(x_1282)) {
 x_1283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1283 = x_1282;
}
lean_ctor_set(x_1283, 0, x_1280);
lean_ctor_set(x_1283, 1, x_1281);
return x_1283;
}
}
}
}
else
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
lean_dec(x_1088);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1284 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1284 = lean_box(0);
}
x_1285 = l_Lean_Syntax_inhabited;
x_1286 = lean_array_get(x_1285, x_11, x_1083);
x_1287 = l_Lean_Syntax_getArgs(x_1286);
lean_dec(x_1286);
x_1288 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1289 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_1287, x_1288, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_1287);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 lean_ctor_release(x_1289, 1);
 x_1292 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1292 = lean_box(0);
}
x_1293 = l_Lean_nullKind;
if (lean_is_scalar(x_1284)) {
 x_1294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1294 = x_1284;
}
lean_ctor_set(x_1294, 0, x_1293);
lean_ctor_set(x_1294, 1, x_1290);
x_1295 = lean_array_set(x_11, x_1083, x_1294);
x_1296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1296, 0, x_10);
lean_ctor_set(x_1296, 1, x_1295);
if (lean_is_scalar(x_1292)) {
 x_1297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1297 = x_1292;
}
lean_ctor_set(x_1297, 0, x_1296);
lean_ctor_set(x_1297, 1, x_1291);
return x_1297;
}
else
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
lean_dec(x_1284);
lean_dec(x_11);
lean_dec(x_10);
x_1298 = lean_ctor_get(x_1289, 0);
lean_inc(x_1298);
x_1299 = lean_ctor_get(x_1289, 1);
lean_inc(x_1299);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 lean_ctor_release(x_1289, 1);
 x_1300 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1300 = lean_box(0);
}
if (lean_is_scalar(x_1300)) {
 x_1301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1301 = x_1300;
}
lean_ctor_set(x_1301, 0, x_1298);
lean_ctor_set(x_1301, 1, x_1299);
return x_1301;
}
}
}
else
{
lean_object* x_1302; lean_object* x_1303; 
lean_dec(x_1088);
lean_dec(x_11);
lean_dec(x_10);
x_1302 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1303 = l_Lean_Elab_Term_CollectPatternVars_processCtorApp(x_1302, x_1, x_2, x_1100, x_4, x_5, x_6, x_1072, x_8, x_1087);
lean_dec(x_1);
return x_1303;
}
}
}
}
case 3:
{
lean_object* x_1311; lean_object* x_1312; 
x_1311 = l___private_Lean_Elab_Match_28__collect___main___closed__11;
x_1312 = l___private_Lean_Elab_Match_25__processId(x_1311, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1312;
}
default: 
{
lean_object* x_1313; 
lean_dec(x_1);
x_1313 = l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1313;
}
}
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_28__collect___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_28__collect___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_28__collect___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_28__collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_28__collect___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_Syntax_getPos(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_FileMap_toPosition(x_16, x_20);
x_22 = lean_box(0);
x_23 = l_String_splitAux___main___closed__1;
lean_inc(x_15);
x_24 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_3);
x_25 = lean_st_ref_take(x_6, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 2);
x_30 = l_Std_PersistentArray_push___rarg(x_29, x_24);
lean_ctor_set(x_26, 2, x_30);
x_31 = lean_st_ref_set(x_6, x_26, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_43 = l_Std_PersistentArray_push___rarg(x_40, x_24);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_42);
x_45 = lean_st_ref_set(x_6, x_44, x_27);
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
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_ctor_get(x_5, 0);
x_52 = lean_ctor_get(x_5, 1);
x_53 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_FileMap_toPosition(x_52, x_50);
x_57 = lean_box(0);
x_58 = l_String_splitAux___main___closed__1;
lean_inc(x_51);
x_59 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_3);
x_60 = lean_st_ref_take(x_6, x_55);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_61, 2);
x_65 = l_Std_PersistentArray_push___rarg(x_64, x_59);
lean_ctor_set(x_61, 2, x_65);
x_66 = lean_st_ref_set(x_6, x_61, x_62);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_61, 0);
x_74 = lean_ctor_get(x_61, 1);
x_75 = lean_ctor_get(x_61, 2);
x_76 = lean_ctor_get(x_61, 3);
x_77 = lean_ctor_get(x_61, 4);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_61);
x_78 = l_Std_PersistentArray_push___rarg(x_75, x_59);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_77);
x_80 = lean_st_ref_set(x_6, x_79, x_62);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = 0;
x_13 = l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("collecting variables at pattern: ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_21 = l_Lean_checkTraceOption(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_Match_28__collect___main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
x_27 = x_23;
x_28 = lean_array_fset(x_17, x_1, x_27);
lean_dec(x_1);
x_1 = x_26;
x_2 = x_28;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
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
lean_inc(x_18);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_18);
x_35 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_20, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_Match_28__collect___main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_1, x_42);
x_44 = x_40;
x_45 = lean_array_fset(x_17, x_1, x_44);
lean_dec(x_1);
x_1 = x_43;
x_2 = x_45;
x_10 = x_41;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
x_16 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4), 10, 2);
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
x_33 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4), 10, 2);
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
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* _init_l___private_Lean_Elab_Match_29__collectPatternVars___closed__1() {
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
lean_object* l___private_Lean_Elab_Match_29__collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l___private_Lean_Elab_Match_29__collectPatternVars___closed__1;
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
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_17, 2);
lean_dec(x_20);
x_21 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_17, 2, x_21);
x_22 = lean_st_ref_set(x_10, x_17, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_7);
x_24 = l_Lean_Meta_mkFreshExprMVarWithIdImpl(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_7);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_st_ref_set(x_10, x_35, x_18);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_7);
x_38 = l_Lean_Meta_mkFreshExprMVarWithIdImpl(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_7);
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
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_18 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_3);
x_24 = l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__1(x_15, x_21, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = l_Lean_Expr_fvarId_x21(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_array_push(x_2, x_16);
x_18 = l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg(x_3, x_4, x_14, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_19 = l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg(x_4, x_5, x_15, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__2(x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_inc(x_5);
x_26 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(x_24, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_2);
x_30 = 0;
x_31 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(x_23, x_30, x_27, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
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
lean_inc(x_5);
x_35 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(x_33, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_5);
x_38 = l_Lean_Elab_Term_mkFreshUserName(x_5, x_6, x_7, x_8, x_9, x_10, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__2___boxed), 13, 5);
lean_closure_set(x_41, 0, x_3);
lean_closure_set(x_41, 1, x_32);
lean_closure_set(x_41, 2, x_4);
lean_closure_set(x_41, 3, x_1);
lean_closure_set(x_41, 4, x_2);
x_42 = 0;
x_43 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(x_39, x_42, x_36, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
return x_43;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__withPatternVarsAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_30__withPatternVarsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_30__withPatternVarsAux___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_31__withPatternVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_Match_30__withPatternVarsAux___main___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_31__withPatternVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_31__withPatternVars___rarg), 9, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected match type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_16 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_fget(x_1, x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Term_elabTermEnsuringType(x_21, x_22, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_29 = lean_expr_instantiate1(x_20, x_25);
lean_dec(x_20);
x_30 = lean_array_push(x_4, x_25);
x_2 = x_28;
x_3 = x_29;
x_4 = x_30;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__3;
x_38 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_32__elabPatternsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_32__elabPatternsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_32__elabPatternsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_32__elabPatternsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_7, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
x_20 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_16, 2, x_20);
x_21 = lean_st_ref_set(x_7, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_10, x_4, x_5, x_6, x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_1, 3, x_24);
x_26 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = l_Lean_TraceState_Inhabited___closed__1;
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_st_ref_set(x_7, x_34, x_17);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_10, x_4, x_5, x_6, x_7, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_ctor_set(x_1, 3, x_38);
x_40 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_39);
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
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_ctor_get(x_1, 3);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_49 = lean_st_ref_get(x_7, x_8);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_take(x_7, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 3, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_st_ref_set(x_7, x_60, x_55);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_47, x_4, x_5, x_6, x_7, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_66, 0, x_44);
lean_ctor_set(x_66, 1, x_45);
lean_ctor_set(x_66, 2, x_46);
lean_ctor_set(x_66, 3, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_48);
x_67 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_65);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_1);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_ctor_get(x_1, 3);
x_73 = lean_ctor_get(x_1, 4);
x_74 = lean_st_ref_get(x_7, x_8);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_take(x_7, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_82 = lean_ctor_get(x_79, 2);
lean_dec(x_82);
x_83 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_79, 2, x_83);
x_84 = lean_st_ref_set(x_7, x_79, x_80);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_72, x_4, x_5, x_6, x_7, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_73, x_4, x_5, x_6, x_7, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_ctor_set(x_1, 4, x_90);
lean_ctor_set(x_1, 3, x_87);
x_92 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_97 = lean_ctor_get(x_79, 0);
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_79);
x_99 = l_Lean_TraceState_Inhabited___closed__1;
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_st_ref_set(x_7, x_100, x_80);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_72, x_4, x_5, x_6, x_7, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_73, x_4, x_5, x_6, x_7, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_ctor_set(x_1, 4, x_107);
lean_ctor_set(x_1, 3, x_104);
x_109 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_108);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_113 = lean_ctor_get(x_1, 0);
x_114 = lean_ctor_get(x_1, 1);
x_115 = lean_ctor_get(x_1, 2);
x_116 = lean_ctor_get(x_1, 3);
x_117 = lean_ctor_get(x_1, 4);
x_118 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_1);
x_119 = lean_st_ref_get(x_7, x_8);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 2);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_take(x_7, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 3, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
x_131 = lean_st_ref_set(x_7, x_130, x_125);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_116, x_4, x_5, x_6, x_7, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_117, x_4, x_5, x_6, x_7, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_139, 0, x_113);
lean_ctor_set(x_139, 1, x_114);
lean_ctor_set(x_139, 2, x_115);
lean_ctor_set(x_139, 3, x_134);
lean_ctor_set(x_139, 4, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*5, x_118);
x_140 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_138);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: mvarId: ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fvarId: ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_18);
x_20 = l_Lean_mkMVar(x_18);
lean_inc(x_5);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_68 = lean_ctor_get(x_9, 0);
x_69 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_70 = l_Lean_checkTraceOption(x_68, x_69);
if (x_70 == 0)
{
lean_dec(x_18);
x_24 = x_23;
goto block_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_18);
x_72 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6;
x_73 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___lambda__1___closed__1;
x_75 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_22);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_22);
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_19);
x_80 = l_Lean_mkFVar(x_19);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_69, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_24 = x_84;
goto block_67;
}
block_67:
{
if (lean_obj_tag(x_22) == 2)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_19);
x_26 = l_Lean_mkFVar(x_19);
lean_inc(x_5);
lean_inc(x_26);
lean_inc(x_25);
x_27 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_25, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_9, 0);
x_30 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_31 = l_Lean_checkTraceOption(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_7);
lean_inc(x_5);
x_32 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_5);
x_35 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_array_push(x_4, x_36);
x_3 = x_17;
x_4 = x_38;
x_11 = x_37;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = l_Lean_mkMVar(x_25);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___lambda__1___closed__1;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_26);
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_30, x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
lean_inc(x_7);
lean_inc(x_5);
x_54 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_5);
x_57 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_array_push(x_4, x_58);
x_3 = x_17;
x_4 = x_60;
x_11 = x_59;
goto _start;
}
else
{
uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_19);
x_3 = x_17;
x_11 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_15, 0);
lean_inc(x_85);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_5);
x_86 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_5__mkUserNameFor___spec__1(x_85, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_5);
x_89 = l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_87, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_array_push(x_4, x_90);
x_3 = x_17;
x_4 = x_92;
x_11 = x_91;
goto _start;
}
else
{
uint8_t x_94; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2(x_1, x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
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
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
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
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_33__alreadyVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_Match_33__alreadyVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_33__alreadyVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_34__markAsVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_Match_34__markAsVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_34__markAsVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = lean_ctor_get(x_3, 6);
lean_inc(x_11);
lean_inc(x_11);
x_12 = l_Lean_Elab_getBetterRef(x_10, x_11);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_dec(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
x_14 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Elab_addMacroStack(x_1, x_11);
x_23 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_22, x_5, x_6, x_7, x_8, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_tag(x_23, 1);
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_indentExpr(x_1);
x_11 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_15, 2, x_19);
x_20 = lean_st_ref_set(x_8, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_metavar_ctx_get_expr_assignment(x_25, x_1);
x_27 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_st_ref_set(x_8, x_35, x_16);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_6, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_metavar_ctx_get_expr_assignment(x_41, x_1);
x_43 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
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
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
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
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_ctor_set(x_14, 1, x_5);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_st_ref_set(x_1, x_25, x_15);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
lean_inc(x_31);
lean_inc(x_30);
x_32 = lean_name_mk_numeral(x_30, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_31, x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_st_ref_take(x_1, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 2);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 3, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_40);
x_43 = lean_st_ref_set(x_1, x_42, x_38);
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
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg___boxed), 2, 0);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_15, 2, x_19);
x_20 = lean_st_ref_set(x_8, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 2);
x_25 = lean_ctor_get(x_7, 3);
x_26 = lean_nat_dec_eq(x_23, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_23, x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
x_30 = l_Lean_Meta_inferTypeRef;
x_31 = lean_st_ref_get(x_30, x_21);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_34 = lean_apply_6(x_32, x_1, x_5, x_6, x_29, x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_1);
x_49 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_50 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_49, x_5, x_6, x_7, x_8, x_21);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = l_Lean_TraceState_Inhabited___closed__1;
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_st_ref_set(x_8, x_61, x_16);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
x_66 = lean_ctor_get(x_7, 2);
x_67 = lean_ctor_get(x_7, 3);
x_68 = lean_nat_dec_eq(x_65, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_65, x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_64);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_67);
x_72 = l_Lean_Meta_inferTypeRef;
x_73 = lean_st_ref_get(x_72, x_63);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_76 = lean_apply_6(x_74, x_1, x_5, x_6, x_71, x_8, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
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
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_dec(x_76);
x_85 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_84);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_89 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_90 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_89, x_5, x_6, x_7, x_8, x_63);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_92);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
x_20 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_16, 2, x_20);
x_21 = lean_st_ref_set(x_9, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = l_Lean_MetavarContext_assignExpr(x_27, x_1, x_2);
lean_ctor_set(x_24, 0, x_28);
x_29 = lean_st_ref_set(x_7, x_24, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
x_40 = lean_ctor_get(x_24, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_41 = l_Lean_MetavarContext_assignExpr(x_38, x_1, x_2);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
x_43 = lean_st_ref_set(x_7, x_42, x_25);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
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
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = l_Lean_TraceState_Inhabited___closed__1;
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_st_ref_set(x_9, x_53, x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_7, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l_Lean_MetavarContext_assignExpr(x_59, x_1, x_2);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 3, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
x_65 = lean_st_ref_set(x_7, x_64, x_58);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_36__mkLocalDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Expr_mvarId_x21(x_1);
x_11 = lean_st_ref_get(x_2, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_10);
x_13 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Meta_inferType___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
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
lean_inc(x_3);
x_23 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__4(x_10, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_mkFreshUserName(x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
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
x_37 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5(x_1, x_35, x_28);
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
x_60 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5(x_1, x_58, x_28);
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
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_36__mkLocalDeclFor___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_36__mkLocalDeclFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_36__mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_15, 2, x_19);
x_20 = lean_st_ref_set(x_8, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 2);
x_25 = lean_ctor_get(x_7, 3);
x_26 = lean_nat_dec_eq(x_23, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_23, x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
x_30 = l_Lean_Meta_whnfRef;
x_31 = lean_st_ref_get(x_30, x_21);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_34 = lean_apply_6(x_32, x_1, x_5, x_6, x_29, x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_1);
x_49 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_50 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_49, x_5, x_6, x_7, x_8, x_21);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = l_Lean_TraceState_Inhabited___closed__1;
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_st_ref_set(x_8, x_61, x_16);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
x_66 = lean_ctor_get(x_7, 2);
x_67 = lean_ctor_get(x_7, 3);
x_68 = lean_nat_dec_eq(x_65, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_65, x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_64);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_67);
x_72 = l_Lean_Meta_whnfRef;
x_73 = lean_st_ref_get(x_72, x_63);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_76 = lean_apply_6(x_74, x_1, x_5, x_6, x_71, x_8, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
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
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_dec(x_76);
x_85 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_84);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_89 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_90 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_89, x_5, x_6, x_7, x_8, x_63);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_92);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_34 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of auxiliary declaration 'namedPattern'");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_12 = l___private_Lean_Elab_Match_28__collect___main___closed__8;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity___main(x_1, x_12, x_13);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_25 = l_Lean_Expr_getAppFn___main(x_1);
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
x_33 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_37 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_36);
x_38 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
lean_inc(x_1);
x_42 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_39, x_41);
x_43 = lean_array_get_size(x_42);
x_44 = lean_ctor_get(x_35, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 4);
lean_inc(x_45);
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
x_47 = lean_nat_dec_eq(x_43, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_35);
lean_dec(x_27);
x_48 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_53 = l_Array_extract___rarg(x_42, x_36, x_44);
x_54 = l_Array_extract___rarg(x_42, x_44, x_43);
lean_dec(x_43);
lean_dec(x_42);
x_55 = x_54;
x_56 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2), 10, 2);
lean_closure_set(x_56, 0, x_36);
lean_closure_set(x_56, 1, x_55);
x_57 = x_56;
x_58 = lean_apply_8(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_35, 0);
lean_inc(x_59);
lean_dec(x_35);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Array_toList___rarg(x_53);
lean_dec(x_53);
x_64 = l_Array_toList___rarg(x_61);
lean_dec(x_61);
x_65 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_27);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_58, 0, x_65);
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_58, 0);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_58);
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
x_69 = l_Array_toList___rarg(x_53);
lean_dec(x_53);
x_70 = l_Array_toList___rarg(x_66);
lean_dec(x_66);
x_71 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_27);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_53);
lean_dec(x_35);
lean_dec(x_27);
x_73 = !lean_is_exclusive(x_58);
if (x_73 == 0)
{
return x_58;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_58, 0);
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_58);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_34);
lean_dec(x_27);
x_77 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_25);
x_78 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_20);
if (x_79 == 0)
{
return x_20;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_20, 0);
x_81 = lean_ctor_get(x_20, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_20);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
x_83 = l___private_Lean_Elab_Match_36__mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_84 = l_Lean_Expr_fvarId_x21(x_1);
x_104 = lean_st_ref_get(x_2, x_9);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
x_108 = lean_array_get_size(x_107);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(x_84, x_105, x_107, x_108, x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_105);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_84);
x_111 = l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_106);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
x_85 = x_106;
goto block_103;
}
block_103:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l___private_Lean_Elab_Match_33__alreadyVisited(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_inc(x_84);
x_90 = l___private_Lean_Elab_Match_34__markAsVisited(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_84);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_86);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_86, 0);
lean_dec(x_98);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_86, 0, x_99);
return x_86;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_86, 1);
lean_inc(x_100);
lean_dec(x_86);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_1);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_9);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_1);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_9);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_1);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_9);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_122);
x_124 = lean_unsigned_to_nat(2u);
x_125 = lean_nat_sub(x_123, x_124);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_125, x_126);
lean_dec(x_125);
x_128 = l_Lean_Expr_getRevArg_x21___main(x_1, x_127);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_129 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
x_133 = lean_nat_sub(x_123, x_126);
lean_dec(x_123);
x_134 = lean_nat_sub(x_133, x_126);
lean_dec(x_133);
x_135 = l_Lean_Expr_getRevArg_x21___main(x_1, x_134);
lean_dec(x_1);
if (lean_obj_tag(x_135) == 1)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_131);
lean_ctor_set(x_129, 0, x_137);
return x_129;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_135);
lean_free_object(x_129);
lean_dec(x_131);
x_138 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_139 = l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg(x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_129, 0);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_129);
x_142 = lean_nat_sub(x_123, x_126);
lean_dec(x_123);
x_143 = lean_nat_sub(x_142, x_126);
lean_dec(x_142);
x_144 = l_Lean_Expr_getRevArg_x21___main(x_1, x_143);
lean_dec(x_1);
if (lean_obj_tag(x_144) == 1)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_144);
lean_dec(x_140);
x_148 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_149 = l_Lean_throwError___at___private_Lean_Elab_Match_35__throwInvalidPattern___spec__1___rarg(x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_123);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_129);
if (x_150 == 0)
{
return x_129;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_129, 0);
x_152 = lean_ctor_get(x_129, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_129);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_1);
x_154 = lean_ctor_get(x_11, 0);
lean_inc(x_154);
lean_dec(x_11);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_155);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_1);
x_169 = lean_ctor_get(x_10, 0);
lean_inc(x_169);
lean_dec(x_10);
if (lean_obj_tag(x_169) == 1)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_st_ref_get(x_2, x_9);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_ctor_get(x_171, 1);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
x_176 = lean_array_get_size(x_175);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_170, x_173, x_175, x_176, x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_173);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_169);
lean_ctor_set(x_171, 0, x_179);
return x_171;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_free_object(x_171);
x_180 = l___private_Lean_Elab_Match_33__alreadyVisited(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_174);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = l___private_Lean_Elab_Match_34__markAsVisited(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_184, 0);
lean_dec(x_186);
x_187 = l_Lean_Expr_fvarId_x21(x_169);
lean_dec(x_169);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_184, 0, x_188);
return x_184;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_dec(x_184);
x_190 = l_Lean_Expr_fvarId_x21(x_169);
lean_dec(x_169);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_189);
return x_192;
}
}
else
{
uint8_t x_193; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_193 = !lean_is_exclusive(x_180);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_180, 0);
lean_dec(x_194);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_169);
lean_ctor_set(x_180, 0, x_195);
return x_180;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_180, 1);
lean_inc(x_196);
lean_dec(x_180);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_169);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_199 = lean_ctor_get(x_171, 0);
x_200 = lean_ctor_get(x_171, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_171);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
x_202 = lean_array_get_size(x_201);
x_203 = lean_unsigned_to_nat(0u);
x_204 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_170, x_199, x_201, x_202, x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_199);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_169);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_200);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = l___private_Lean_Elab_Match_33__alreadyVisited(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_200);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
x_211 = l___private_Lean_Elab_Match_34__markAsVisited(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_210);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Expr_fvarId_x21(x_169);
lean_dec(x_169);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
if (lean_is_scalar(x_213)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_213;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_212);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_ctor_get(x_207, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_218 = x_207;
} else {
 lean_dec_ref(x_207);
 x_218 = lean_box(0);
}
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_169);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
return x_220;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_169);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_9);
return x_222;
}
}
}
}
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
lean_inc(x_3);
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
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2), 10, 2);
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
x_28 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed), 9, 2);
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
x_35 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(x_31, x_31, x_12, x_34);
x_36 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_31, x_31, x_12, x_35);
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
x_41 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(x_31, x_31, x_12, x_39);
x_42 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_31, x_31, x_12, x_41);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_37__withElaboratedLHS___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
lean_inc(x_3);
x_18 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_32__elabPatternsAux___boxed), 11, 4);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Elab_Term_withSynthesize___rarg(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_6);
x_21 = l_Lean_Elab_Term_finalizePatternDecls(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = x_19;
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_37__withElaboratedLHS___spec__1___boxed), 9, 2);
lean_closure_set(x_25, 0, x_13);
lean_closure_set(x_25, 1, x_24);
x_26 = x_25;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = lean_apply_7(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___lambda__1___boxed), 12, 3);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_20);
x_31 = l_Lean_Elab_Term_withDepElimPatterns___rarg(x_22, x_28, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
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
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_37__withElaboratedLHS___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_37__withElaboratedLHS___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_1, x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_System_FilePath_dirName___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_7);
x_10 = l_List_reprAux___main___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_List_reprAux___main___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_19, x_6);
lean_dec(x_6);
return x_20;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; 
x_21 = l_String_splitAux___main___closed__1;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = 0;
x_25 = l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_24, x_23);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_System_FilePath_dirName___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_26);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_30);
x_33 = l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = lean_string_append(x_34, x_25);
lean_dec(x_25);
return x_35;
}
}
}
}
}
lean_object* l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rhs: ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_elabTermEnsuringType(x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
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
lean_free_object(x_15);
lean_inc(x_7);
lean_inc(x_5);
x_28 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1(x_26, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
lean_inc(x_2);
x_33 = l_Lean_checkTraceOption(x_32, x_2);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_free_object(x_28);
lean_inc(x_30);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_30);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
x_47 = lean_ctor_get(x_9, 0);
lean_inc(x_47);
lean_inc(x_2);
x_48 = l_Lean_checkTraceOption(x_47, x_2);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_45);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_45);
x_52 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_53, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_45);
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
else
{
uint8_t x_59; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_26);
x_63 = l_Lean_mkThunk(x_17);
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_inc(x_2);
x_65 = l_Lean_checkTraceOption(x_64, x_2);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_15, 0, x_66);
return x_15;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_free_object(x_15);
lean_inc(x_63);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_63);
x_68 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_3);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_63);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_15, 0);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_15);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = l_List_redLength___main___rarg(x_79);
x_81 = lean_mk_empty_array_with_capacity(x_80);
lean_dec(x_80);
x_82 = l_List_toArrayAux___main___rarg(x_79, x_81);
x_83 = x_82;
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_84, x_83);
x_86 = x_85;
x_87 = l_Array_isEmpty___rarg(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
lean_inc(x_7);
lean_inc(x_5);
x_88 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1(x_86, x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
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
x_92 = lean_ctor_get(x_9, 0);
lean_inc(x_92);
lean_inc(x_2);
x_93 = l_Lean_checkTraceOption(x_92, x_2);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_3);
lean_ctor_set(x_94, 1, x_89);
if (lean_is_scalar(x_91)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_91;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_90);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_91);
lean_inc(x_89);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_89);
x_97 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_98 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_98, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_3);
lean_ctor_set(x_102, 1, x_89);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_88, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_88, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_106 = x_88;
} else {
 lean_dec_ref(x_88);
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
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_86);
x_108 = l_Lean_mkThunk(x_77);
x_109 = lean_ctor_get(x_9, 0);
lean_inc(x_109);
lean_inc(x_2);
x_110 = l_Lean_checkTraceOption(x_109, x_2);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_3);
lean_ctor_set(x_111, 1, x_108);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_78);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_inc(x_108);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_108);
x_114 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_115, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_108);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_15);
if (x_121 == 0)
{
return x_15;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_15, 0);
x_123 = lean_ctor_get(x_15, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_15);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__1), 11, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
x_15 = l___private_Lean_Elab_Match_37__withElaboratedLHS___rarg(x_12, x_4, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("patternVars: ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatchAltView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabMatchAltView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabMatchAltView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 3);
x_14 = l_Lean_replaceRef(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_replaceRef(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_inc(x_12);
lean_ctor_set(x_7, 3, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l___private_Lean_Elab_Match_29__collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_23 = l_Lean_checkTraceOption(x_12, x_22);
lean_dec(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 11, 3);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
x_25 = l___private_Lean_Elab_Match_31__withPatternVars___rarg(x_20, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = l_Array_toList___rarg(x_20);
x_27 = l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_26);
x_28 = l_Array_HasRepr___rarg___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_Elab_Term_elabMatchAltView___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_22, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 11, 3);
lean_closure_set(x_36, 0, x_21);
lean_closure_set(x_36, 1, x_22);
lean_closure_set(x_36, 2, x_2);
x_37 = l___private_Lean_Elab_Match_31__withPatternVars___rarg(x_20, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
x_44 = lean_ctor_get(x_7, 2);
x_45 = lean_ctor_get(x_7, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_46 = l_Lean_replaceRef(x_10, x_45);
lean_dec(x_10);
x_47 = l_Lean_replaceRef(x_46, x_45);
lean_dec(x_46);
x_48 = l_Lean_replaceRef(x_47, x_45);
lean_dec(x_45);
lean_dec(x_47);
lean_inc(x_42);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_8);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_Elab_Match_29__collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_49, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_56 = l_Lean_checkTraceOption(x_42, x_55);
lean_dec(x_42);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 11, 3);
lean_closure_set(x_57, 0, x_54);
lean_closure_set(x_57, 1, x_55);
lean_closure_set(x_57, 2, x_2);
x_58 = l___private_Lean_Elab_Match_31__withPatternVars___rarg(x_53, x_57, x_3, x_4, x_5, x_6, x_49, x_8, x_52);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = l_Array_toList___rarg(x_53);
x_60 = l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_59);
x_61 = l_Array_HasRepr___rarg___closed__1;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_Elab_Term_elabMatchAltView___closed__3;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_55, x_66, x_3, x_4, x_5, x_6, x_49, x_8, x_52);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 11, 3);
lean_closure_set(x_69, 0, x_54);
lean_closure_set(x_69, 1, x_55);
lean_closure_set(x_69, 2, x_2);
x_70 = l___private_Lean_Elab_Match_31__withPatternVars___rarg(x_53, x_69, x_3, x_4, x_5, x_6, x_49, x_8, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_49);
lean_dec(x_42);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_73 = x_50;
} else {
 lean_dec_ref(x_50);
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
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabMatchAltView___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkSort(x_11);
x_14 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* _init_l_Lean_Elab_Term_mkMotiveType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkMotiveType___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_mkMotiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lean_Elab_Term_mkMotiveType___closed__1;
x_12 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg(x_1, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_mkMotiveType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_mkMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_Meta_Match_mkMatcher(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_34 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = l_Lean_TraceState_Inhabited___closed__1;
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_st_ref_set(x_10, x_42, x_18);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l_Lean_Meta_Match_mkMatcher(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_mkMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = l_Nat_repr(x_7);
x_9 = l_Array_HasRepr___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = l_Nat_repr(x_15);
x_17 = l_Array_HasRepr___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing cases:");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unused alternatives: ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_counterExamplesToMessageData(x_9);
x_12 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__4;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_9);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_List_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = l_List_map___main___at_Lean_Elab_Term_reportMatcherResultErrors___spec__1(x_19);
x_22 = l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Term_reportMatcherResultErrors___closed__7;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_19__elabImplicitLambdaAux___spec__1___boxed), 9, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchType: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Elab_Match_6__elabMatchTypeAndDiscrs(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_expandMacrosInPatterns(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_110 = lean_ctor_get(x_9, 0);
lean_inc(x_110);
x_111 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_112 = l_Lean_checkTraceOption(x_110, x_111);
lean_dec(x_110);
if (x_112 == 0)
{
x_20 = x_19;
goto block_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_inc(x_16);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_16);
x_114 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__8;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_111, x_115, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_20 = x_117;
goto block_109;
}
block_109:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = x_18;
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_23 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__1), 10, 3);
lean_closure_set(x_23, 0, x_16);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_21);
x_24 = x_23;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = lean_apply_7(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = x_26;
lean_inc(x_28);
x_29 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__2(x_22, x_28);
x_30 = x_29;
x_31 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_38__elabMatchAux___spec__3(x_22, x_28);
x_32 = x_31;
x_33 = lean_array_get_size(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_33);
lean_inc(x_16);
x_34 = l_Lean_Elab_Term_mkMotiveType(x_16, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_33);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
x_38 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___rarg(x_16, x_37, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__2;
lean_inc(x_5);
x_43 = l_Lean_Elab_Term_mkAuxName(x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Array_toList___rarg(x_32);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_47 = l_Lean_Elab_Term_mkMatcher(x_44, x_35, x_33, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_5);
lean_inc(x_48);
x_50 = l_Lean_Elab_Term_reportMatcherResultErrors(x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l_Lean_mkApp(x_54, x_40);
x_56 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_15, x_15, x_22, x_55);
lean_dec(x_15);
x_57 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_30, x_30, x_22, x_56);
lean_dec(x_30);
x_58 = lean_ctor_get(x_9, 0);
lean_inc(x_58);
x_59 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_60 = l_Lean_checkTraceOption(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_50);
lean_inc(x_57);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_57);
x_62 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__5;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_59, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_57);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
lean_dec(x_50);
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
lean_dec(x_48);
x_71 = l_Lean_mkApp(x_70, x_40);
x_72 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_15, x_15, x_22, x_71);
lean_dec(x_15);
x_73 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_30, x_30, x_22, x_72);
lean_dec(x_30);
x_74 = lean_ctor_get(x_9, 0);
lean_inc(x_74);
x_75 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
x_76 = l_Lean_checkTraceOption(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_73);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_79 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__5;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_75, x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_50);
if (x_85 == 0)
{
return x_50;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_50, 0);
x_87 = lean_ctor_get(x_50, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_50);
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
lean_dec(x_40);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = !lean_is_exclusive(x_47);
if (x_89 == 0)
{
return x_47;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_47, 0);
x_91 = lean_ctor_get(x_47, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_47);
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
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = !lean_is_exclusive(x_43);
if (x_93 == 0)
{
return x_43;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_43, 0);
x_95 = lean_ctor_get(x_43, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_43);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_39);
if (x_97 == 0)
{
return x_39;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_39, 0);
x_99 = lean_ctor_get(x_39, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_39);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_34);
if (x_101 == 0)
{
return x_34;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_34, 0);
x_103 = lean_ctor_get(x_34, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_34);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_105 = !lean_is_exclusive(x_25);
if (x_105 == 0)
{
return x_25;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_25, 0);
x_107 = lean_ctor_get(x_25, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_25);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_118 = !lean_is_exclusive(x_17);
if (x_118 == 0)
{
return x_17;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_17, 0);
x_120 = lean_ctor_get(x_17, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_17);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_12);
if (x_122 == 0)
{
return x_12;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_12, 0);
x_124 = lean_ctor_get(x_12, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_12);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_38__elabMatchAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_39__waitExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
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
x_13 = l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_Match_39__waitExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_39__waitExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_40__elabMatchCore___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_9, x_10);
lean_dec(x_9);
x_12 = lean_nat_add(x_1, x_10);
x_13 = x_11;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Match_40__elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_Match_39__waitExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_empty___closed__1;
x_19 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_16, x_15, x_17, x_18);
lean_dec(x_15);
x_20 = x_19;
x_21 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_40__elabMatchCore___spec__1(x_17, x_20);
x_22 = x_21;
x_23 = l___private_Lean_Elab_Match_8__getMatchAlts(x_1);
x_24 = l_Lean_Syntax_getArg(x_1, x_16);
x_25 = l___private_Lean_Elab_Match_38__elabMatchAux(x_22, x_23, x_24, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_40__elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_40__elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__26;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("→");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__13;
x_2 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
if (x_6 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__12;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_12);
lean_ctor_set(x_3, 1, x_4);
x_14 = lean_array_fget(x_1, x_2);
x_15 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_17 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_2 = x_17;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_20 = l___private_Lean_Elab_Match_41__mkMatchType___main(x_1, x_19, x_3, x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_14, x_23);
x_25 = l_Lean_Syntax_isNone(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_26 = l_Lean_Syntax_getArg(x_14, x_7);
lean_dec(x_14);
x_27 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_28 = l_Lean_addMacroScope(x_12, x_27, x_4);
x_29 = lean_box(0);
x_30 = l_Lean_SourceInfo_inhabited___closed__1;
x_31 = l_Lean_Elab_Term_mkFreshUserName___closed__2;
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
x_33 = l_Array_empty___closed__1;
lean_inc(x_32);
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_nullKind___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
x_38 = lean_array_push(x_37, x_36);
x_39 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2;
x_40 = lean_array_push(x_38, x_39);
x_41 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_42 = lean_array_push(x_40, x_41);
x_43 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
x_44 = lean_array_push(x_42, x_43);
x_45 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_33, x_46);
x_48 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4;
x_49 = lean_array_push(x_47, x_48);
x_50 = lean_array_push(x_33, x_26);
x_51 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__19;
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_push(x_52, x_32);
x_54 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__18;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_33, x_55);
x_57 = lean_array_push(x_56, x_48);
x_58 = lean_array_push(x_57, x_22);
x_59 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_49, x_60);
x_62 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_20, 0, x_63);
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_64 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5;
x_65 = lean_array_push(x_64, x_22);
x_66 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_20, 0, x_67);
return x_20;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_20, 0);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_20);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_14, x_70);
x_72 = l_Lean_Syntax_isNone(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_73 = l_Lean_Syntax_getArg(x_14, x_7);
lean_dec(x_14);
x_74 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_75 = l_Lean_addMacroScope(x_12, x_74, x_4);
x_76 = lean_box(0);
x_77 = l_Lean_SourceInfo_inhabited___closed__1;
x_78 = l_Lean_Elab_Term_mkFreshUserName___closed__2;
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
x_80 = l_Array_empty___closed__1;
lean_inc(x_79);
x_81 = lean_array_push(x_80, x_79);
x_82 = l_Lean_nullKind___closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
x_85 = lean_array_push(x_84, x_83);
x_86 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2;
x_87 = lean_array_push(x_85, x_86);
x_88 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_89 = lean_array_push(x_87, x_88);
x_90 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
x_91 = lean_array_push(x_89, x_90);
x_92 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_80, x_93);
x_95 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4;
x_96 = lean_array_push(x_94, x_95);
x_97 = lean_array_push(x_80, x_73);
x_98 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__19;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_array_push(x_99, x_79);
x_101 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__18;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_80, x_102);
x_104 = lean_array_push(x_103, x_95);
x_105 = lean_array_push(x_104, x_68);
x_106 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_96, x_107);
x_109 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_69);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_112 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5;
x_113 = lean_array_push(x_112, x_68);
x_114 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_69);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_3, 0);
x_118 = lean_ctor_get(x_3, 2);
x_119 = lean_ctor_get(x_3, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_117);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_4);
lean_ctor_set(x_120, 2, x_118);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_array_fget(x_1, x_2);
x_122 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_inc(x_121);
x_123 = l_Lean_Syntax_isOfKind(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_4);
x_124 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_2 = x_124;
x_3 = x_120;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_126 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_127 = l___private_Lean_Elab_Match_41__mkMatchType___main(x_1, x_126, x_120, x_8);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_unsigned_to_nat(0u);
x_132 = l_Lean_Syntax_getArg(x_121, x_131);
x_133 = l_Lean_Syntax_isNone(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_134 = l_Lean_Syntax_getArg(x_121, x_7);
lean_dec(x_121);
x_135 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_136 = l_Lean_addMacroScope(x_117, x_135, x_4);
x_137 = lean_box(0);
x_138 = l_Lean_SourceInfo_inhabited___closed__1;
x_139 = l_Lean_Elab_Term_mkFreshUserName___closed__2;
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_136);
lean_ctor_set(x_140, 3, x_137);
x_141 = l_Array_empty___closed__1;
lean_inc(x_140);
x_142 = lean_array_push(x_141, x_140);
x_143 = l_Lean_nullKind___closed__2;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
x_146 = lean_array_push(x_145, x_144);
x_147 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2;
x_148 = lean_array_push(x_146, x_147);
x_149 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_150 = lean_array_push(x_148, x_149);
x_151 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
x_152 = lean_array_push(x_150, x_151);
x_153 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_array_push(x_141, x_154);
x_156 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4;
x_157 = lean_array_push(x_155, x_156);
x_158 = lean_array_push(x_141, x_134);
x_159 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__19;
x_160 = lean_array_push(x_158, x_159);
x_161 = lean_array_push(x_160, x_140);
x_162 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__18;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_array_push(x_141, x_163);
x_165 = lean_array_push(x_164, x_156);
x_166 = lean_array_push(x_165, x_128);
x_167 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_push(x_157, x_168);
x_170 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
if (lean_is_scalar(x_130)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_130;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_129);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_4);
x_173 = l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5;
x_174 = lean_array_push(x_173, x_128);
x_175 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
if (lean_is_scalar(x_130)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_130;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_129);
return x_177;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_41__mkMatchType___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_41__mkMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_41__mkMatchType___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_41__mkMatchType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_41__mkMatchType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_42__mkOptType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_List_reprAux___main___rarg___closed__1;
x_3 = l_Lean_mkAtomFrom(x_1, x_2);
x_4 = l_Lean_mkAppStx___closed__9;
x_5 = lean_array_push(x_4, x_3);
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_mkOptionalNode___closed__2;
x_10 = lean_array_push(x_9, x_8);
x_11 = l_Lean_nullKind;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
lean_object* _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq.refl");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_14 = lean_array_push(x_3, x_9);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_19 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_9);
x_20 = l_Lean_Syntax_setArg(x_9, x_16, x_19);
x_21 = lean_array_push(x_3, x_20);
x_22 = l_List_reprAux___main___rarg___closed__1;
x_23 = l_Lean_mkAtomFrom(x_9, x_22);
lean_dec(x_9);
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
x_28 = l_Lean_addMacroScope(x_26, x_27, x_25);
x_29 = l_Lean_SourceInfo_inhabited___closed__1;
x_30 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__3;
x_31 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__5;
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__14;
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Lean_mkAppStx___closed__8;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__1;
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_push(x_24, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_2, x_43);
lean_dec(x_2);
x_2 = x_44;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_2, x_46);
lean_dec(x_2);
x_48 = lean_array_push(x_3, x_9);
x_2 = x_47;
x_3 = x_48;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_43__mkNewDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_43__mkNewDiscrs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Match_44__mkNewPatterns___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid number of patterns, expected #");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_14 = l_Nat_repr(x_8);
x_15 = l___private_Lean_Elab_Match_44__mkNewPatterns___main___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_8);
x_19 = lean_array_fget(x_3, x_4);
x_20 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_inc(x_11);
x_21 = l_Lean_Syntax_isOfKind(x_11, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_24 = lean_array_push(x_5, x_19);
x_4 = x_23;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_11, x_26);
lean_dec(x_11);
x_28 = l_Lean_Syntax_isNone(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_19);
x_29 = lean_array_push(x_5, x_19);
x_30 = l_List_reprAux___main___rarg___closed__1;
x_31 = l_Lean_mkAtomFrom(x_19, x_30);
lean_dec(x_19);
x_32 = lean_array_push(x_29, x_31);
x_33 = l_Lean_Syntax_getArg(x_27, x_26);
lean_dec(x_27);
x_34 = lean_array_push(x_32, x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_4 = x_36;
x_5 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_4, x_38);
lean_dec(x_4);
x_40 = lean_array_push(x_5, x_19);
x_4 = x_39;
x_5 = x_40;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_44__mkNewPatterns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_44__mkNewPatterns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_44__mkNewPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_44__mkNewPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_45__mkNewAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = l_Array_empty___closed__1;
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Match_44__mkNewPatterns___main(x_2, x_1, x_7, x_5, x_8, x_3, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_nullKind;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Syntax_setArg(x_2, x_5, x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = l_Lean_nullKind;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = l_Lean_Syntax_setArg(x_2, x_5, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_45__mkNewAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_45__mkNewAlt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_46__mkNewAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_1, x_3);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_mod(x_3, x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = lean_array_push(x_4, x_10);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_inc(x_2);
lean_inc(x_5);
x_19 = lean_apply_3(x_2, x_10, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_24 = lean_array_push(x_4, x_20);
x_3 = x_23;
x_4 = x_24;
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_46__mkNewAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_46__mkNewAlts___spec__2(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_46__mkNewAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_45__mkNewAlt___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_46__mkNewAlts___spec__1(x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_46__mkNewAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Match_46__mkNewAlts___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_46__mkNewAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_46__mkNewAlts___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_46__mkNewAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_46__mkNewAlts(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match expected type should not be provided when discriminants with equality proofs are used");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_empty___closed__1;
x_10 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_7, x_6, x_8, x_9);
x_11 = lean_array_get_size(x_10);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___spec__1(x_1, x_10, x_11, x_8);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Syntax_getArg(x_1, x_7);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Match_41__mkMatchType___main(x_6, x_8, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_copyInfo(x_21, x_1);
x_24 = l___private_Lean_Elab_Match_42__mkOptType(x_23);
x_25 = l_Lean_Syntax_setArg(x_1, x_7, x_24);
lean_inc(x_2);
x_26 = l___private_Lean_Elab_Match_43__mkNewDiscrs___main(x_6, x_8, x_9, x_2, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_nullKind;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = l_Lean_Syntax_setArg(x_25, x_4, x_30);
x_32 = lean_unsigned_to_nat(4u);
x_33 = l_Lean_Syntax_getArg(x_31, x_32);
x_34 = l_Lean_Syntax_getArg(x_33, x_4);
x_35 = l_Lean_Syntax_getArgs(x_34);
lean_dec(x_34);
x_36 = l___private_Lean_Elab_Match_46__mkNewAlts(x_6, x_35, x_2, x_28);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Syntax_setArg(x_33, x_4, x_39);
x_41 = l_Lean_Syntax_setArg(x_31, x_32, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_36, 0, x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Syntax_setArg(x_33, x_4, x_45);
x_47 = l_Lean_Syntax_setArg(x_31, x_32, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_33);
lean_dec(x_31);
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_36, 0);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_36);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_37; lean_object* x_1493; uint8_t x_1494; 
x_1493 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
lean_inc(x_1);
x_1494 = l_Lean_Syntax_isOfKind(x_1, x_1493);
if (x_1494 == 0)
{
uint8_t x_1495; 
x_1495 = 0;
x_37 = x_1495;
goto block_1492;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; uint8_t x_1499; 
x_1496 = l_Lean_Syntax_getArgs(x_1);
x_1497 = lean_array_get_size(x_1496);
lean_dec(x_1496);
x_1498 = lean_unsigned_to_nat(5u);
x_1499 = lean_nat_dec_eq(x_1497, x_1498);
lean_dec(x_1497);
x_37 = x_1499;
goto block_1492;
}
block_36:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_40__elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 6);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_3, 6, x_17);
x_18 = 1;
x_19 = l_Lean_Elab_Term_elabTerm(x_13, x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get(x_3, 3);
x_24 = lean_ctor_get(x_3, 4);
x_25 = lean_ctor_get(x_3, 5);
x_26 = lean_ctor_get(x_3, 6);
x_27 = lean_ctor_get(x_3, 7);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_13);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set(x_33, 4, x_24);
lean_ctor_set(x_33, 5, x_25);
lean_ctor_set(x_33, 6, x_32);
lean_ctor_set(x_33, 7, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 1, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 2, x_30);
x_34 = 1;
x_35 = l_Lean_Elab_Term_elabTerm(x_13, x_2, x_34, x_33, x_4, x_5, x_6, x_7, x_8, x_11);
return x_35;
}
}
}
block_1492:
{
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_8, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_4, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 2);
lean_inc(x_50);
x_51 = lean_environment_main_module(x_44);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
lean_inc(x_1);
x_53 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_52, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_take(x_4, x_47);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 3);
lean_dec(x_60);
lean_ctor_set(x_57, 3, x_55);
x_61 = lean_st_ref_set(x_4, x_57, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_10 = x_54;
x_11 = x_62;
goto block_36;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
x_65 = lean_ctor_get(x_57, 2);
x_66 = lean_ctor_get(x_57, 4);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_55);
lean_ctor_set(x_67, 4, x_66);
x_68 = lean_st_ref_set(x_4, x_67, x_58);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_10 = x_54;
x_11 = x_69;
goto block_36;
}
}
else
{
lean_object* x_70; 
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_53, 0);
lean_inc(x_70);
lean_dec(x_53);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_71, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_71);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_47);
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
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_1486; uint8_t x_1487; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = l_Lean_Syntax_getArg(x_1, x_85);
x_1486 = l_Lean_nullKind___closed__2;
lean_inc(x_86);
x_1487 = l_Lean_Syntax_isOfKind(x_86, x_1486);
if (x_1487 == 0)
{
uint8_t x_1488; 
x_1488 = 0;
x_87 = x_1488;
goto block_1485;
}
else
{
lean_object* x_1489; lean_object* x_1490; uint8_t x_1491; 
x_1489 = l_Lean_Syntax_getArgs(x_86);
x_1490 = lean_array_get_size(x_1489);
lean_dec(x_1489);
x_1491 = lean_nat_dec_eq(x_1490, x_85);
lean_dec(x_1490);
x_87 = x_1491;
goto block_1485;
}
block_1485:
{
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_86);
x_88 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_8, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_4, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 3);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_7, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_7, 2);
lean_inc(x_100);
x_101 = lean_environment_main_module(x_94);
x_102 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_89);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_100);
lean_inc(x_1);
x_103 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_102, x_98);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_take(x_4, x_97);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 3);
lean_dec(x_110);
lean_ctor_set(x_107, 3, x_105);
x_111 = lean_st_ref_set(x_4, x_107, x_108);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_10 = x_104;
x_11 = x_112;
goto block_36;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
x_115 = lean_ctor_get(x_107, 2);
x_116 = lean_ctor_get(x_107, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_115);
lean_ctor_set(x_117, 3, x_105);
lean_ctor_set(x_117, 4, x_116);
x_118 = lean_st_ref_set(x_4, x_117, x_108);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_10 = x_104;
x_11 = x_119;
goto block_36;
}
}
else
{
lean_object* x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_103, 0);
lean_inc(x_120);
lean_dec(x_103);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_121, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_121);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_object* x_130; uint8_t x_131; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_97);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
return x_130;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_130);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_1478; uint8_t x_1479; 
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Lean_Syntax_getArg(x_86, x_135);
lean_dec(x_86);
x_1478 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_inc(x_136);
x_1479 = l_Lean_Syntax_isOfKind(x_136, x_1478);
if (x_1479 == 0)
{
uint8_t x_1480; 
x_1480 = 0;
x_137 = x_1480;
goto block_1477;
}
else
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; uint8_t x_1484; 
x_1481 = l_Lean_Syntax_getArgs(x_136);
x_1482 = lean_array_get_size(x_1481);
lean_dec(x_1481);
x_1483 = lean_unsigned_to_nat(2u);
x_1484 = lean_nat_dec_eq(x_1482, x_1483);
lean_dec(x_1482);
x_137 = x_1484;
goto block_1477;
}
block_1477:
{
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_136);
x_138 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_st_ref_get(x_8, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_get(x_4, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 3);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_7, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_7, 2);
lean_inc(x_150);
x_151 = lean_environment_main_module(x_144);
x_152 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_139);
lean_ctor_set(x_152, 2, x_149);
lean_ctor_set(x_152, 3, x_150);
lean_inc(x_1);
x_153 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_152, x_148);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_st_ref_take(x_4, x_147);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 3);
lean_dec(x_160);
lean_ctor_set(x_157, 3, x_155);
x_161 = lean_st_ref_set(x_4, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_10 = x_154;
x_11 = x_162;
goto block_36;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_157, 0);
x_164 = lean_ctor_get(x_157, 1);
x_165 = lean_ctor_get(x_157, 2);
x_166 = lean_ctor_get(x_157, 4);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_164);
lean_ctor_set(x_167, 2, x_165);
lean_ctor_set(x_167, 3, x_155);
lean_ctor_set(x_167, 4, x_166);
x_168 = lean_st_ref_set(x_4, x_167, x_158);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_10 = x_154;
x_11 = x_169;
goto block_36;
}
}
else
{
lean_object* x_170; 
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_153, 0);
lean_inc(x_170);
lean_dec(x_153);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_171, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_171);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
return x_175;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_175);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
else
{
lean_object* x_180; uint8_t x_181; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_147);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
return x_180;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_180);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
lean_object* x_185; uint8_t x_186; lean_object* x_1471; uint8_t x_1472; 
x_185 = l_Lean_Syntax_getArg(x_136, x_135);
x_1471 = l_Lean_nullKind___closed__2;
lean_inc(x_185);
x_1472 = l_Lean_Syntax_isOfKind(x_185, x_1471);
if (x_1472 == 0)
{
uint8_t x_1473; 
lean_dec(x_185);
x_1473 = 0;
x_186 = x_1473;
goto block_1470;
}
else
{
lean_object* x_1474; lean_object* x_1475; uint8_t x_1476; 
x_1474 = l_Lean_Syntax_getArgs(x_185);
lean_dec(x_185);
x_1475 = lean_array_get_size(x_1474);
lean_dec(x_1474);
x_1476 = lean_nat_dec_eq(x_1475, x_135);
lean_dec(x_1475);
x_186 = x_1476;
goto block_1470;
}
block_1470:
{
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_136);
x_187 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_st_ref_get(x_8, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_st_ref_get(x_4, x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 3);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_7, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_7, 2);
lean_inc(x_199);
x_200 = lean_environment_main_module(x_193);
x_201 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_188);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_199);
lean_inc(x_1);
x_202 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_201, x_197);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_st_ref_take(x_4, x_196);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_206, 3);
lean_dec(x_209);
lean_ctor_set(x_206, 3, x_204);
x_210 = lean_st_ref_set(x_4, x_206, x_207);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_10 = x_203;
x_11 = x_211;
goto block_36;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_212 = lean_ctor_get(x_206, 0);
x_213 = lean_ctor_get(x_206, 1);
x_214 = lean_ctor_get(x_206, 2);
x_215 = lean_ctor_get(x_206, 4);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_206);
x_216 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_213);
lean_ctor_set(x_216, 2, x_214);
lean_ctor_set(x_216, 3, x_204);
lean_ctor_set(x_216, 4, x_215);
x_217 = lean_st_ref_set(x_4, x_216, x_207);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_10 = x_203;
x_11 = x_218;
goto block_36;
}
}
else
{
lean_object* x_219; 
lean_dec(x_2);
lean_dec(x_1);
x_219 = lean_ctor_get(x_202, 0);
lean_inc(x_219);
lean_dec(x_202);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_224 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_220, x_223, x_3, x_4, x_5, x_6, x_7, x_8, x_196);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_220);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
return x_224;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_224, 0);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_224);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
else
{
lean_object* x_229; uint8_t x_230; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_229 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_196);
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
return x_229;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_229);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_902; uint8_t x_903; uint8_t x_904; 
x_234 = l_Lean_Syntax_getArg(x_136, x_85);
lean_dec(x_136);
x_235 = lean_unsigned_to_nat(2u);
x_236 = l_Lean_Syntax_getArg(x_1, x_235);
x_902 = l_Lean_nullKind___closed__2;
lean_inc(x_236);
x_903 = l_Lean_Syntax_isOfKind(x_236, x_902);
if (x_903 == 0)
{
uint8_t x_1466; 
x_1466 = 0;
x_904 = x_1466;
goto block_1465;
}
else
{
lean_object* x_1467; lean_object* x_1468; uint8_t x_1469; 
x_1467 = l_Lean_Syntax_getArgs(x_236);
x_1468 = lean_array_get_size(x_1467);
lean_dec(x_1467);
x_1469 = lean_nat_dec_eq(x_1468, x_135);
lean_dec(x_1468);
x_904 = x_1469;
goto block_1465;
}
block_901:
{
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_236);
lean_dec(x_234);
x_238 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_st_ref_get(x_8, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_st_ref_get(x_4, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 3);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_7, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_7, 2);
lean_inc(x_250);
x_251 = lean_environment_main_module(x_244);
x_252 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_239);
lean_ctor_set(x_252, 2, x_249);
lean_ctor_set(x_252, 3, x_250);
lean_inc(x_1);
x_253 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_252, x_248);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_st_ref_take(x_4, x_247);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = !lean_is_exclusive(x_257);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_257, 3);
lean_dec(x_260);
lean_ctor_set(x_257, 3, x_255);
x_261 = lean_st_ref_set(x_4, x_257, x_258);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
x_10 = x_254;
x_11 = x_262;
goto block_36;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_ctor_get(x_257, 0);
x_264 = lean_ctor_get(x_257, 1);
x_265 = lean_ctor_get(x_257, 2);
x_266 = lean_ctor_get(x_257, 4);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_257);
x_267 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_267, 0, x_263);
lean_ctor_set(x_267, 1, x_264);
lean_ctor_set(x_267, 2, x_265);
lean_ctor_set(x_267, 3, x_255);
lean_ctor_set(x_267, 4, x_266);
x_268 = lean_st_ref_set(x_4, x_267, x_258);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_10 = x_254;
x_11 = x_269;
goto block_36;
}
}
else
{
lean_object* x_270; 
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_253, 0);
lean_inc(x_270);
lean_dec(x_253);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_271, x_274, x_3, x_4, x_5, x_6, x_7, x_8, x_247);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_271);
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
return x_275;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_275, 0);
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_275);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
else
{
lean_object* x_280; uint8_t x_281; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_247);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
return x_280;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_280);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
else
{
lean_object* x_285; uint8_t x_286; lean_object* x_895; uint8_t x_896; 
x_285 = l_Lean_Syntax_getArg(x_236, x_135);
lean_dec(x_236);
x_895 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_inc(x_285);
x_896 = l_Lean_Syntax_isOfKind(x_285, x_895);
if (x_896 == 0)
{
uint8_t x_897; 
x_897 = 0;
x_286 = x_897;
goto block_894;
}
else
{
lean_object* x_898; lean_object* x_899; uint8_t x_900; 
x_898 = l_Lean_Syntax_getArgs(x_285);
x_899 = lean_array_get_size(x_898);
lean_dec(x_898);
x_900 = lean_nat_dec_eq(x_899, x_235);
lean_dec(x_899);
x_286 = x_900;
goto block_894;
}
block_894:
{
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_285);
lean_dec(x_234);
x_287 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_st_ref_get(x_8, x_289);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_st_ref_get(x_4, x_292);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = lean_ctor_get(x_295, 3);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get(x_7, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_7, 2);
lean_inc(x_299);
x_300 = lean_environment_main_module(x_293);
x_301 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_288);
lean_ctor_set(x_301, 2, x_298);
lean_ctor_set(x_301, 3, x_299);
lean_inc(x_1);
x_302 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_301, x_297);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_st_ref_take(x_4, x_296);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_306, 3);
lean_dec(x_309);
lean_ctor_set(x_306, 3, x_304);
x_310 = lean_st_ref_set(x_4, x_306, x_307);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_10 = x_303;
x_11 = x_311;
goto block_36;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_306, 0);
x_313 = lean_ctor_get(x_306, 1);
x_314 = lean_ctor_get(x_306, 2);
x_315 = lean_ctor_get(x_306, 4);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_306);
x_316 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_316, 0, x_312);
lean_ctor_set(x_316, 1, x_313);
lean_ctor_set(x_316, 2, x_314);
lean_ctor_set(x_316, 3, x_304);
lean_ctor_set(x_316, 4, x_315);
x_317 = lean_st_ref_set(x_4, x_316, x_307);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_10 = x_303;
x_11 = x_318;
goto block_36;
}
}
else
{
lean_object* x_319; 
lean_dec(x_2);
lean_dec(x_1);
x_319 = lean_ctor_get(x_302, 0);
lean_inc(x_319);
lean_dec(x_302);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_322, 0, x_321);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_324 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_320, x_323, x_3, x_4, x_5, x_6, x_7, x_8, x_296);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_320);
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
return x_324;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_324, 0);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_324);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
else
{
lean_object* x_329; uint8_t x_330; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_329 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_296);
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
return x_329;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_329, 0);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_329);
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
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_888; uint8_t x_889; 
x_334 = l_Lean_Syntax_getArg(x_285, x_85);
lean_dec(x_285);
x_335 = lean_unsigned_to_nat(4u);
x_336 = l_Lean_Syntax_getArg(x_1, x_335);
x_888 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
lean_inc(x_336);
x_889 = l_Lean_Syntax_isOfKind(x_336, x_888);
if (x_889 == 0)
{
uint8_t x_890; 
x_890 = 0;
x_337 = x_890;
goto block_887;
}
else
{
lean_object* x_891; lean_object* x_892; uint8_t x_893; 
x_891 = l_Lean_Syntax_getArgs(x_336);
x_892 = lean_array_get_size(x_891);
lean_dec(x_891);
x_893 = lean_nat_dec_eq(x_892, x_235);
lean_dec(x_892);
x_337 = x_893;
goto block_887;
}
block_887:
{
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_336);
lean_dec(x_334);
lean_dec(x_234);
x_338 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_st_ref_get(x_8, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_st_ref_get(x_4, x_343);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_346, 3);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_7, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_7, 2);
lean_inc(x_350);
x_351 = lean_environment_main_module(x_344);
x_352 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_339);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_350);
lean_inc(x_1);
x_353 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_352, x_348);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_st_ref_take(x_4, x_347);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = !lean_is_exclusive(x_357);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_357, 3);
lean_dec(x_360);
lean_ctor_set(x_357, 3, x_355);
x_361 = lean_st_ref_set(x_4, x_357, x_358);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_10 = x_354;
x_11 = x_362;
goto block_36;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_363 = lean_ctor_get(x_357, 0);
x_364 = lean_ctor_get(x_357, 1);
x_365 = lean_ctor_get(x_357, 2);
x_366 = lean_ctor_get(x_357, 4);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_357);
x_367 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_367, 0, x_363);
lean_ctor_set(x_367, 1, x_364);
lean_ctor_set(x_367, 2, x_365);
lean_ctor_set(x_367, 3, x_355);
lean_ctor_set(x_367, 4, x_366);
x_368 = lean_st_ref_set(x_4, x_367, x_358);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_10 = x_354;
x_11 = x_369;
goto block_36;
}
}
else
{
lean_object* x_370; 
lean_dec(x_2);
lean_dec(x_1);
x_370 = lean_ctor_get(x_353, 0);
lean_inc(x_370);
lean_dec(x_353);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_375 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_371, x_374, x_3, x_4, x_5, x_6, x_7, x_8, x_347);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_371);
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
return x_375;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_375, 0);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_375);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
else
{
lean_object* x_380; uint8_t x_381; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_380 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_347);
x_381 = !lean_is_exclusive(x_380);
if (x_381 == 0)
{
return x_380;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_380, 0);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_380);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
else
{
lean_object* x_385; uint8_t x_386; lean_object* x_656; uint8_t x_657; uint8_t x_658; 
x_385 = l_Lean_Syntax_getArg(x_336, x_135);
x_656 = l_Lean_nullKind___closed__2;
lean_inc(x_385);
x_657 = l_Lean_Syntax_isOfKind(x_385, x_656);
if (x_657 == 0)
{
uint8_t x_883; 
x_883 = 0;
x_658 = x_883;
goto block_882;
}
else
{
lean_object* x_884; lean_object* x_885; uint8_t x_886; 
x_884 = l_Lean_Syntax_getArgs(x_385);
x_885 = lean_array_get_size(x_884);
lean_dec(x_884);
x_886 = lean_nat_dec_eq(x_885, x_135);
lean_dec(x_885);
x_658 = x_886;
goto block_882;
}
block_655:
{
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_336);
lean_dec(x_334);
lean_dec(x_234);
x_387 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_st_ref_get(x_8, x_389);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_ctor_get(x_391, 0);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_st_ref_get(x_4, x_392);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = lean_ctor_get(x_395, 3);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_ctor_get(x_7, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_7, 2);
lean_inc(x_399);
x_400 = lean_environment_main_module(x_393);
x_401 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_388);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_399);
lean_inc(x_1);
x_402 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_401, x_397);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_st_ref_take(x_4, x_396);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = !lean_is_exclusive(x_406);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_406, 3);
lean_dec(x_409);
lean_ctor_set(x_406, 3, x_404);
x_410 = lean_st_ref_set(x_4, x_406, x_407);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_10 = x_403;
x_11 = x_411;
goto block_36;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_412 = lean_ctor_get(x_406, 0);
x_413 = lean_ctor_get(x_406, 1);
x_414 = lean_ctor_get(x_406, 2);
x_415 = lean_ctor_get(x_406, 4);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_406);
x_416 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_416, 0, x_412);
lean_ctor_set(x_416, 1, x_413);
lean_ctor_set(x_416, 2, x_414);
lean_ctor_set(x_416, 3, x_404);
lean_ctor_set(x_416, 4, x_415);
x_417 = lean_st_ref_set(x_4, x_416, x_407);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_10 = x_403;
x_11 = x_418;
goto block_36;
}
}
else
{
lean_object* x_419; 
lean_dec(x_2);
lean_dec(x_1);
x_419 = lean_ctor_get(x_402, 0);
lean_inc(x_419);
lean_dec(x_402);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_422, 0, x_421);
x_423 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_423, 0, x_422);
x_424 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_420, x_423, x_3, x_4, x_5, x_6, x_7, x_8, x_396);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_420);
x_425 = !lean_is_exclusive(x_424);
if (x_425 == 0)
{
return x_424;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_424, 0);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_424);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
else
{
lean_object* x_429; uint8_t x_430; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_429 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_396);
x_430 = !lean_is_exclusive(x_429);
if (x_430 == 0)
{
return x_429;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_429, 0);
x_432 = lean_ctor_get(x_429, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_429);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
else
{
lean_object* x_434; uint8_t x_435; lean_object* x_649; uint8_t x_650; 
x_434 = l_Lean_Syntax_getArg(x_336, x_85);
lean_dec(x_336);
x_649 = l_Lean_nullKind___closed__2;
lean_inc(x_434);
x_650 = l_Lean_Syntax_isOfKind(x_434, x_649);
if (x_650 == 0)
{
uint8_t x_651; 
x_651 = 0;
x_435 = x_651;
goto block_648;
}
else
{
lean_object* x_652; lean_object* x_653; uint8_t x_654; 
x_652 = l_Lean_Syntax_getArgs(x_434);
x_653 = lean_array_get_size(x_652);
lean_dec(x_652);
x_654 = lean_nat_dec_eq(x_653, x_85);
lean_dec(x_653);
x_435 = x_654;
goto block_648;
}
block_648:
{
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_434);
lean_dec(x_334);
lean_dec(x_234);
x_436 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_st_ref_get(x_8, x_438);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_ctor_get(x_440, 0);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_st_ref_get(x_4, x_441);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_ctor_get(x_444, 3);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_ctor_get(x_7, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_7, 2);
lean_inc(x_448);
x_449 = lean_environment_main_module(x_442);
x_450 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_437);
lean_ctor_set(x_450, 2, x_447);
lean_ctor_set(x_450, 3, x_448);
lean_inc(x_1);
x_451 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_450, x_446);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_st_ref_take(x_4, x_445);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_457 = !lean_is_exclusive(x_455);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_455, 3);
lean_dec(x_458);
lean_ctor_set(x_455, 3, x_453);
x_459 = lean_st_ref_set(x_4, x_455, x_456);
x_460 = lean_ctor_get(x_459, 1);
lean_inc(x_460);
lean_dec(x_459);
x_10 = x_452;
x_11 = x_460;
goto block_36;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_461 = lean_ctor_get(x_455, 0);
x_462 = lean_ctor_get(x_455, 1);
x_463 = lean_ctor_get(x_455, 2);
x_464 = lean_ctor_get(x_455, 4);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_455);
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_461);
lean_ctor_set(x_465, 1, x_462);
lean_ctor_set(x_465, 2, x_463);
lean_ctor_set(x_465, 3, x_453);
lean_ctor_set(x_465, 4, x_464);
x_466 = lean_st_ref_set(x_4, x_465, x_456);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_10 = x_452;
x_11 = x_467;
goto block_36;
}
}
else
{
lean_object* x_468; 
lean_dec(x_2);
lean_dec(x_1);
x_468 = lean_ctor_get(x_451, 0);
lean_inc(x_468);
lean_dec(x_451);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_471, 0, x_470);
x_472 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_472, 0, x_471);
x_473 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_469, x_472, x_3, x_4, x_5, x_6, x_7, x_8, x_445);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_469);
x_474 = !lean_is_exclusive(x_473);
if (x_474 == 0)
{
return x_473;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_473, 0);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_473);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
else
{
lean_object* x_478; uint8_t x_479; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_478 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_445);
x_479 = !lean_is_exclusive(x_478);
if (x_479 == 0)
{
return x_478;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_478, 0);
x_481 = lean_ctor_get(x_478, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_478);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
}
else
{
lean_object* x_483; uint8_t x_484; lean_object* x_641; uint8_t x_642; 
x_483 = l_Lean_Syntax_getArg(x_434, x_135);
lean_dec(x_434);
x_641 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_483);
x_642 = l_Lean_Syntax_isOfKind(x_483, x_641);
if (x_642 == 0)
{
uint8_t x_643; 
x_643 = 0;
x_484 = x_643;
goto block_640;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; 
x_644 = l_Lean_Syntax_getArgs(x_483);
x_645 = lean_array_get_size(x_644);
lean_dec(x_644);
x_646 = lean_unsigned_to_nat(3u);
x_647 = lean_nat_dec_eq(x_645, x_646);
lean_dec(x_645);
x_484 = x_647;
goto block_640;
}
block_640:
{
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_483);
lean_dec(x_334);
lean_dec(x_234);
x_485 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_st_ref_get(x_8, x_487);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_ctor_get(x_489, 0);
lean_inc(x_491);
lean_dec(x_489);
x_492 = lean_st_ref_get(x_4, x_490);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_495 = lean_ctor_get(x_493, 3);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_7, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_7, 2);
lean_inc(x_497);
x_498 = lean_environment_main_module(x_491);
x_499 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_486);
lean_ctor_set(x_499, 2, x_496);
lean_ctor_set(x_499, 3, x_497);
lean_inc(x_1);
x_500 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_499, x_495);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_st_ref_take(x_4, x_494);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = !lean_is_exclusive(x_504);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_504, 3);
lean_dec(x_507);
lean_ctor_set(x_504, 3, x_502);
x_508 = lean_st_ref_set(x_4, x_504, x_505);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
x_10 = x_501;
x_11 = x_509;
goto block_36;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_504, 0);
x_511 = lean_ctor_get(x_504, 1);
x_512 = lean_ctor_get(x_504, 2);
x_513 = lean_ctor_get(x_504, 4);
lean_inc(x_513);
lean_inc(x_512);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_504);
x_514 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_514, 0, x_510);
lean_ctor_set(x_514, 1, x_511);
lean_ctor_set(x_514, 2, x_512);
lean_ctor_set(x_514, 3, x_502);
lean_ctor_set(x_514, 4, x_513);
x_515 = lean_st_ref_set(x_4, x_514, x_505);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_10 = x_501;
x_11 = x_516;
goto block_36;
}
}
else
{
lean_object* x_517; 
lean_dec(x_2);
lean_dec(x_1);
x_517 = lean_ctor_get(x_500, 0);
lean_inc(x_517);
lean_dec(x_500);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_520 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_520, 0, x_519);
x_521 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_521, 0, x_520);
x_522 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_518, x_521, x_3, x_4, x_5, x_6, x_7, x_8, x_494);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_518);
x_523 = !lean_is_exclusive(x_522);
if (x_523 == 0)
{
return x_522;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_522, 0);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_522);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
else
{
lean_object* x_527; uint8_t x_528; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_527 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_494);
x_528 = !lean_is_exclusive(x_527);
if (x_528 == 0)
{
return x_527;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_527, 0);
x_530 = lean_ctor_get(x_527, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_527);
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
lean_object* x_532; uint8_t x_533; lean_object* x_634; uint8_t x_635; 
x_532 = l_Lean_Syntax_getArg(x_483, x_135);
x_634 = l_Lean_nullKind___closed__2;
lean_inc(x_532);
x_635 = l_Lean_Syntax_isOfKind(x_532, x_634);
if (x_635 == 0)
{
uint8_t x_636; 
x_636 = 0;
x_533 = x_636;
goto block_633;
}
else
{
lean_object* x_637; lean_object* x_638; uint8_t x_639; 
x_637 = l_Lean_Syntax_getArgs(x_532);
x_638 = lean_array_get_size(x_637);
lean_dec(x_637);
x_639 = lean_nat_dec_eq(x_638, x_85);
lean_dec(x_638);
x_533 = x_639;
goto block_633;
}
block_633:
{
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_532);
lean_dec(x_483);
lean_dec(x_334);
lean_dec(x_234);
x_534 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = lean_st_ref_get(x_8, x_536);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get(x_538, 0);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_st_ref_get(x_4, x_539);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_544 = lean_ctor_get(x_542, 3);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_ctor_get(x_7, 1);
lean_inc(x_545);
x_546 = lean_ctor_get(x_7, 2);
lean_inc(x_546);
x_547 = lean_environment_main_module(x_540);
x_548 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_535);
lean_ctor_set(x_548, 2, x_545);
lean_ctor_set(x_548, 3, x_546);
lean_inc(x_1);
x_549 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_548, x_544);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = lean_st_ref_take(x_4, x_543);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = !lean_is_exclusive(x_553);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_553, 3);
lean_dec(x_556);
lean_ctor_set(x_553, 3, x_551);
x_557 = lean_st_ref_set(x_4, x_553, x_554);
x_558 = lean_ctor_get(x_557, 1);
lean_inc(x_558);
lean_dec(x_557);
x_10 = x_550;
x_11 = x_558;
goto block_36;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_559 = lean_ctor_get(x_553, 0);
x_560 = lean_ctor_get(x_553, 1);
x_561 = lean_ctor_get(x_553, 2);
x_562 = lean_ctor_get(x_553, 4);
lean_inc(x_562);
lean_inc(x_561);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_553);
x_563 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_563, 0, x_559);
lean_ctor_set(x_563, 1, x_560);
lean_ctor_set(x_563, 2, x_561);
lean_ctor_set(x_563, 3, x_551);
lean_ctor_set(x_563, 4, x_562);
x_564 = lean_st_ref_set(x_4, x_563, x_554);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
x_10 = x_550;
x_11 = x_565;
goto block_36;
}
}
else
{
lean_object* x_566; 
lean_dec(x_2);
lean_dec(x_1);
x_566 = lean_ctor_get(x_549, 0);
lean_inc(x_566);
lean_dec(x_549);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_569, 0, x_568);
x_570 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_570, 0, x_569);
x_571 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_567, x_570, x_3, x_4, x_5, x_6, x_7, x_8, x_543);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_567);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
return x_571;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_571, 0);
x_574 = lean_ctor_get(x_571, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_571);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
else
{
lean_object* x_576; uint8_t x_577; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_576 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_543);
x_577 = !lean_is_exclusive(x_576);
if (x_577 == 0)
{
return x_576;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_576, 0);
x_579 = lean_ctor_get(x_576, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_576);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
}
}
else
{
lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_581 = l_Lean_Syntax_getArg(x_532, x_135);
lean_dec(x_532);
x_582 = l_Lean_identKind___closed__2;
lean_inc(x_581);
x_583 = l_Lean_Syntax_isOfKind(x_581, x_582);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_581);
lean_dec(x_483);
lean_dec(x_334);
lean_dec(x_234);
x_584 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_587 = lean_st_ref_get(x_8, x_586);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = lean_ctor_get(x_588, 0);
lean_inc(x_590);
lean_dec(x_588);
x_591 = lean_st_ref_get(x_4, x_589);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_ctor_get(x_592, 3);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_ctor_get(x_7, 1);
lean_inc(x_595);
x_596 = lean_ctor_get(x_7, 2);
lean_inc(x_596);
x_597 = lean_environment_main_module(x_590);
x_598 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_585);
lean_ctor_set(x_598, 2, x_595);
lean_ctor_set(x_598, 3, x_596);
lean_inc(x_1);
x_599 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_598, x_594);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = lean_st_ref_take(x_4, x_593);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = !lean_is_exclusive(x_603);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_603, 3);
lean_dec(x_606);
lean_ctor_set(x_603, 3, x_601);
x_607 = lean_st_ref_set(x_4, x_603, x_604);
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
lean_dec(x_607);
x_10 = x_600;
x_11 = x_608;
goto block_36;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_609 = lean_ctor_get(x_603, 0);
x_610 = lean_ctor_get(x_603, 1);
x_611 = lean_ctor_get(x_603, 2);
x_612 = lean_ctor_get(x_603, 4);
lean_inc(x_612);
lean_inc(x_611);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_603);
x_613 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_613, 0, x_609);
lean_ctor_set(x_613, 1, x_610);
lean_ctor_set(x_613, 2, x_611);
lean_ctor_set(x_613, 3, x_601);
lean_ctor_set(x_613, 4, x_612);
x_614 = lean_st_ref_set(x_4, x_613, x_604);
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
x_10 = x_600;
x_11 = x_615;
goto block_36;
}
}
else
{
lean_object* x_616; 
lean_dec(x_2);
lean_dec(x_1);
x_616 = lean_ctor_get(x_599, 0);
lean_inc(x_616);
lean_dec(x_599);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; uint8_t x_622; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_619, 0, x_618);
x_620 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_620, 0, x_619);
x_621 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_617, x_620, x_3, x_4, x_5, x_6, x_7, x_8, x_593);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_617);
x_622 = !lean_is_exclusive(x_621);
if (x_622 == 0)
{
return x_621;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_621, 0);
x_624 = lean_ctor_get(x_621, 1);
lean_inc(x_624);
lean_inc(x_623);
lean_dec(x_621);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
else
{
lean_object* x_626; uint8_t x_627; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_626 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_593);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
return x_626;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_626);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
}
else
{
lean_object* x_631; lean_object* x_632; 
x_631 = l_Lean_Syntax_getArg(x_483, x_235);
lean_dec(x_483);
x_632 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_234, x_581, x_334, x_631, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_632;
}
}
}
}
}
}
}
}
}
block_882:
{
if (x_658 == 0)
{
if (x_657 == 0)
{
uint8_t x_659; 
lean_dec(x_385);
x_659 = 0;
x_386 = x_659;
goto block_655;
}
else
{
lean_object* x_660; lean_object* x_661; uint8_t x_662; 
x_660 = l_Lean_Syntax_getArgs(x_385);
lean_dec(x_385);
x_661 = lean_array_get_size(x_660);
lean_dec(x_660);
x_662 = lean_nat_dec_eq(x_661, x_85);
lean_dec(x_661);
x_386 = x_662;
goto block_655;
}
}
else
{
lean_object* x_663; uint8_t x_664; uint8_t x_877; 
lean_dec(x_385);
x_663 = l_Lean_Syntax_getArg(x_336, x_85);
lean_dec(x_336);
lean_inc(x_663);
x_877 = l_Lean_Syntax_isOfKind(x_663, x_656);
if (x_877 == 0)
{
uint8_t x_878; 
x_878 = 0;
x_664 = x_878;
goto block_876;
}
else
{
lean_object* x_879; lean_object* x_880; uint8_t x_881; 
x_879 = l_Lean_Syntax_getArgs(x_663);
x_880 = lean_array_get_size(x_879);
lean_dec(x_879);
x_881 = lean_nat_dec_eq(x_880, x_85);
lean_dec(x_880);
x_664 = x_881;
goto block_876;
}
block_876:
{
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_663);
lean_dec(x_334);
lean_dec(x_234);
x_665 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
x_668 = lean_st_ref_get(x_8, x_667);
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
x_671 = lean_ctor_get(x_669, 0);
lean_inc(x_671);
lean_dec(x_669);
x_672 = lean_st_ref_get(x_4, x_670);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = lean_ctor_get(x_673, 3);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_ctor_get(x_7, 1);
lean_inc(x_676);
x_677 = lean_ctor_get(x_7, 2);
lean_inc(x_677);
x_678 = lean_environment_main_module(x_671);
x_679 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_679, 0, x_678);
lean_ctor_set(x_679, 1, x_666);
lean_ctor_set(x_679, 2, x_676);
lean_ctor_set(x_679, 3, x_677);
lean_inc(x_1);
x_680 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_679, x_675);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_st_ref_take(x_4, x_674);
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec(x_683);
x_686 = !lean_is_exclusive(x_684);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_684, 3);
lean_dec(x_687);
lean_ctor_set(x_684, 3, x_682);
x_688 = lean_st_ref_set(x_4, x_684, x_685);
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
lean_dec(x_688);
x_10 = x_681;
x_11 = x_689;
goto block_36;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_690 = lean_ctor_get(x_684, 0);
x_691 = lean_ctor_get(x_684, 1);
x_692 = lean_ctor_get(x_684, 2);
x_693 = lean_ctor_get(x_684, 4);
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_691);
lean_inc(x_690);
lean_dec(x_684);
x_694 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_694, 0, x_690);
lean_ctor_set(x_694, 1, x_691);
lean_ctor_set(x_694, 2, x_692);
lean_ctor_set(x_694, 3, x_682);
lean_ctor_set(x_694, 4, x_693);
x_695 = lean_st_ref_set(x_4, x_694, x_685);
x_696 = lean_ctor_get(x_695, 1);
lean_inc(x_696);
lean_dec(x_695);
x_10 = x_681;
x_11 = x_696;
goto block_36;
}
}
else
{
lean_object* x_697; 
lean_dec(x_2);
lean_dec(x_1);
x_697 = lean_ctor_get(x_680, 0);
lean_inc(x_697);
lean_dec(x_680);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
lean_dec(x_697);
x_700 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_700, 0, x_699);
x_701 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_701, 0, x_700);
x_702 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_698, x_701, x_3, x_4, x_5, x_6, x_7, x_8, x_674);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_698);
x_703 = !lean_is_exclusive(x_702);
if (x_703 == 0)
{
return x_702;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_704 = lean_ctor_get(x_702, 0);
x_705 = lean_ctor_get(x_702, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_702);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
return x_706;
}
}
else
{
lean_object* x_707; uint8_t x_708; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_707 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_674);
x_708 = !lean_is_exclusive(x_707);
if (x_708 == 0)
{
return x_707;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_707, 0);
x_710 = lean_ctor_get(x_707, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_707);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
}
else
{
lean_object* x_712; uint8_t x_713; lean_object* x_869; uint8_t x_870; 
x_712 = l_Lean_Syntax_getArg(x_663, x_135);
lean_dec(x_663);
x_869 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_712);
x_870 = l_Lean_Syntax_isOfKind(x_712, x_869);
if (x_870 == 0)
{
uint8_t x_871; 
x_871 = 0;
x_713 = x_871;
goto block_868;
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_872 = l_Lean_Syntax_getArgs(x_712);
x_873 = lean_array_get_size(x_872);
lean_dec(x_872);
x_874 = lean_unsigned_to_nat(3u);
x_875 = lean_nat_dec_eq(x_873, x_874);
lean_dec(x_873);
x_713 = x_875;
goto block_868;
}
block_868:
{
if (x_713 == 0)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_712);
lean_dec(x_334);
lean_dec(x_234);
x_714 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
x_717 = lean_st_ref_get(x_8, x_716);
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = lean_ctor_get(x_718, 0);
lean_inc(x_720);
lean_dec(x_718);
x_721 = lean_st_ref_get(x_4, x_719);
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_724 = lean_ctor_get(x_722, 3);
lean_inc(x_724);
lean_dec(x_722);
x_725 = lean_ctor_get(x_7, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_7, 2);
lean_inc(x_726);
x_727 = lean_environment_main_module(x_720);
x_728 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_715);
lean_ctor_set(x_728, 2, x_725);
lean_ctor_set(x_728, 3, x_726);
lean_inc(x_1);
x_729 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_728, x_724);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_732 = lean_st_ref_take(x_4, x_723);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = !lean_is_exclusive(x_733);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_733, 3);
lean_dec(x_736);
lean_ctor_set(x_733, 3, x_731);
x_737 = lean_st_ref_set(x_4, x_733, x_734);
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
lean_dec(x_737);
x_10 = x_730;
x_11 = x_738;
goto block_36;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_739 = lean_ctor_get(x_733, 0);
x_740 = lean_ctor_get(x_733, 1);
x_741 = lean_ctor_get(x_733, 2);
x_742 = lean_ctor_get(x_733, 4);
lean_inc(x_742);
lean_inc(x_741);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_733);
x_743 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_743, 0, x_739);
lean_ctor_set(x_743, 1, x_740);
lean_ctor_set(x_743, 2, x_741);
lean_ctor_set(x_743, 3, x_731);
lean_ctor_set(x_743, 4, x_742);
x_744 = lean_st_ref_set(x_4, x_743, x_734);
x_745 = lean_ctor_get(x_744, 1);
lean_inc(x_745);
lean_dec(x_744);
x_10 = x_730;
x_11 = x_745;
goto block_36;
}
}
else
{
lean_object* x_746; 
lean_dec(x_2);
lean_dec(x_1);
x_746 = lean_ctor_get(x_729, 0);
lean_inc(x_746);
lean_dec(x_729);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; uint8_t x_752; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec(x_746);
x_749 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_749, 0, x_748);
x_750 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_750, 0, x_749);
x_751 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_747, x_750, x_3, x_4, x_5, x_6, x_7, x_8, x_723);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_747);
x_752 = !lean_is_exclusive(x_751);
if (x_752 == 0)
{
return x_751;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_751, 0);
x_754 = lean_ctor_get(x_751, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_751);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
else
{
lean_object* x_756; uint8_t x_757; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_756 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_723);
x_757 = !lean_is_exclusive(x_756);
if (x_757 == 0)
{
return x_756;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_756, 0);
x_759 = lean_ctor_get(x_756, 1);
lean_inc(x_759);
lean_inc(x_758);
lean_dec(x_756);
x_760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_760, 0, x_758);
lean_ctor_set(x_760, 1, x_759);
return x_760;
}
}
}
}
else
{
lean_object* x_761; uint8_t x_762; uint8_t x_863; 
x_761 = l_Lean_Syntax_getArg(x_712, x_135);
lean_inc(x_761);
x_863 = l_Lean_Syntax_isOfKind(x_761, x_656);
if (x_863 == 0)
{
uint8_t x_864; 
x_864 = 0;
x_762 = x_864;
goto block_862;
}
else
{
lean_object* x_865; lean_object* x_866; uint8_t x_867; 
x_865 = l_Lean_Syntax_getArgs(x_761);
x_866 = lean_array_get_size(x_865);
lean_dec(x_865);
x_867 = lean_nat_dec_eq(x_866, x_85);
lean_dec(x_866);
x_762 = x_867;
goto block_862;
}
block_862:
{
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_761);
lean_dec(x_712);
lean_dec(x_334);
lean_dec(x_234);
x_763 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_763, 1);
lean_inc(x_765);
lean_dec(x_763);
x_766 = lean_st_ref_get(x_8, x_765);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
x_769 = lean_ctor_get(x_767, 0);
lean_inc(x_769);
lean_dec(x_767);
x_770 = lean_st_ref_get(x_4, x_768);
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
x_773 = lean_ctor_get(x_771, 3);
lean_inc(x_773);
lean_dec(x_771);
x_774 = lean_ctor_get(x_7, 1);
lean_inc(x_774);
x_775 = lean_ctor_get(x_7, 2);
lean_inc(x_775);
x_776 = lean_environment_main_module(x_769);
x_777 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_764);
lean_ctor_set(x_777, 2, x_774);
lean_ctor_set(x_777, 3, x_775);
lean_inc(x_1);
x_778 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_777, x_773);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; 
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
x_781 = lean_st_ref_take(x_4, x_772);
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
lean_dec(x_781);
x_784 = !lean_is_exclusive(x_782);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_782, 3);
lean_dec(x_785);
lean_ctor_set(x_782, 3, x_780);
x_786 = lean_st_ref_set(x_4, x_782, x_783);
x_787 = lean_ctor_get(x_786, 1);
lean_inc(x_787);
lean_dec(x_786);
x_10 = x_779;
x_11 = x_787;
goto block_36;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_788 = lean_ctor_get(x_782, 0);
x_789 = lean_ctor_get(x_782, 1);
x_790 = lean_ctor_get(x_782, 2);
x_791 = lean_ctor_get(x_782, 4);
lean_inc(x_791);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_782);
x_792 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_792, 0, x_788);
lean_ctor_set(x_792, 1, x_789);
lean_ctor_set(x_792, 2, x_790);
lean_ctor_set(x_792, 3, x_780);
lean_ctor_set(x_792, 4, x_791);
x_793 = lean_st_ref_set(x_4, x_792, x_783);
x_794 = lean_ctor_get(x_793, 1);
lean_inc(x_794);
lean_dec(x_793);
x_10 = x_779;
x_11 = x_794;
goto block_36;
}
}
else
{
lean_object* x_795; 
lean_dec(x_2);
lean_dec(x_1);
x_795 = lean_ctor_get(x_778, 0);
lean_inc(x_795);
lean_dec(x_778);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; 
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_798, 0, x_797);
x_799 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_799, 0, x_798);
x_800 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_796, x_799, x_3, x_4, x_5, x_6, x_7, x_8, x_772);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_796);
x_801 = !lean_is_exclusive(x_800);
if (x_801 == 0)
{
return x_800;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_800, 0);
x_803 = lean_ctor_get(x_800, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_800);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
else
{
lean_object* x_805; uint8_t x_806; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_805 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_772);
x_806 = !lean_is_exclusive(x_805);
if (x_806 == 0)
{
return x_805;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_807 = lean_ctor_get(x_805, 0);
x_808 = lean_ctor_get(x_805, 1);
lean_inc(x_808);
lean_inc(x_807);
lean_dec(x_805);
x_809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_809, 0, x_807);
lean_ctor_set(x_809, 1, x_808);
return x_809;
}
}
}
}
else
{
lean_object* x_810; lean_object* x_811; uint8_t x_812; 
x_810 = l_Lean_Syntax_getArg(x_761, x_135);
lean_dec(x_761);
x_811 = l_Lean_identKind___closed__2;
lean_inc(x_810);
x_812 = l_Lean_Syntax_isOfKind(x_810, x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_810);
lean_dec(x_712);
lean_dec(x_334);
lean_dec(x_234);
x_813 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec(x_813);
x_816 = lean_st_ref_get(x_8, x_815);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = lean_ctor_get(x_817, 0);
lean_inc(x_819);
lean_dec(x_817);
x_820 = lean_st_ref_get(x_4, x_818);
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
x_823 = lean_ctor_get(x_821, 3);
lean_inc(x_823);
lean_dec(x_821);
x_824 = lean_ctor_get(x_7, 1);
lean_inc(x_824);
x_825 = lean_ctor_get(x_7, 2);
lean_inc(x_825);
x_826 = lean_environment_main_module(x_819);
x_827 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_814);
lean_ctor_set(x_827, 2, x_824);
lean_ctor_set(x_827, 3, x_825);
lean_inc(x_1);
x_828 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_827, x_823);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_831 = lean_st_ref_take(x_4, x_822);
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_834 = !lean_is_exclusive(x_832);
if (x_834 == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_835 = lean_ctor_get(x_832, 3);
lean_dec(x_835);
lean_ctor_set(x_832, 3, x_830);
x_836 = lean_st_ref_set(x_4, x_832, x_833);
x_837 = lean_ctor_get(x_836, 1);
lean_inc(x_837);
lean_dec(x_836);
x_10 = x_829;
x_11 = x_837;
goto block_36;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_838 = lean_ctor_get(x_832, 0);
x_839 = lean_ctor_get(x_832, 1);
x_840 = lean_ctor_get(x_832, 2);
x_841 = lean_ctor_get(x_832, 4);
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_832);
x_842 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_842, 0, x_838);
lean_ctor_set(x_842, 1, x_839);
lean_ctor_set(x_842, 2, x_840);
lean_ctor_set(x_842, 3, x_830);
lean_ctor_set(x_842, 4, x_841);
x_843 = lean_st_ref_set(x_4, x_842, x_833);
x_844 = lean_ctor_get(x_843, 1);
lean_inc(x_844);
lean_dec(x_843);
x_10 = x_829;
x_11 = x_844;
goto block_36;
}
}
else
{
lean_object* x_845; 
lean_dec(x_2);
lean_dec(x_1);
x_845 = lean_ctor_get(x_828, 0);
lean_inc(x_845);
lean_dec(x_828);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; uint8_t x_851; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_848, 0, x_847);
x_849 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_849, 0, x_848);
x_850 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_846, x_849, x_3, x_4, x_5, x_6, x_7, x_8, x_822);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_846);
x_851 = !lean_is_exclusive(x_850);
if (x_851 == 0)
{
return x_850;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = lean_ctor_get(x_850, 0);
x_853 = lean_ctor_get(x_850, 1);
lean_inc(x_853);
lean_inc(x_852);
lean_dec(x_850);
x_854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_854, 0, x_852);
lean_ctor_set(x_854, 1, x_853);
return x_854;
}
}
else
{
lean_object* x_855; uint8_t x_856; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_855 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_822);
x_856 = !lean_is_exclusive(x_855);
if (x_856 == 0)
{
return x_855;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_855, 0);
x_858 = lean_ctor_get(x_855, 1);
lean_inc(x_858);
lean_inc(x_857);
lean_dec(x_855);
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
}
}
else
{
lean_object* x_860; lean_object* x_861; 
x_860 = l_Lean_Syntax_getArg(x_712, x_235);
lean_dec(x_712);
x_861 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_234, x_810, x_334, x_860, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_861;
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
block_1465:
{
if (x_904 == 0)
{
if (x_903 == 0)
{
uint8_t x_905; 
x_905 = 0;
x_237 = x_905;
goto block_901;
}
else
{
lean_object* x_906; lean_object* x_907; uint8_t x_908; 
x_906 = l_Lean_Syntax_getArgs(x_236);
x_907 = lean_array_get_size(x_906);
lean_dec(x_906);
x_908 = lean_nat_dec_eq(x_907, x_85);
lean_dec(x_907);
x_237 = x_908;
goto block_901;
}
}
else
{
lean_object* x_909; lean_object* x_910; uint8_t x_911; lean_object* x_1459; uint8_t x_1460; 
lean_dec(x_236);
x_909 = lean_unsigned_to_nat(4u);
x_910 = l_Lean_Syntax_getArg(x_1, x_909);
x_1459 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
lean_inc(x_910);
x_1460 = l_Lean_Syntax_isOfKind(x_910, x_1459);
if (x_1460 == 0)
{
uint8_t x_1461; 
x_1461 = 0;
x_911 = x_1461;
goto block_1458;
}
else
{
lean_object* x_1462; lean_object* x_1463; uint8_t x_1464; 
x_1462 = l_Lean_Syntax_getArgs(x_910);
x_1463 = lean_array_get_size(x_1462);
lean_dec(x_1462);
x_1464 = lean_nat_dec_eq(x_1463, x_235);
lean_dec(x_1463);
x_911 = x_1464;
goto block_1458;
}
block_1458:
{
if (x_911 == 0)
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_dec(x_910);
lean_dec(x_234);
x_912 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = lean_st_ref_get(x_8, x_914);
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
x_918 = lean_ctor_get(x_916, 0);
lean_inc(x_918);
lean_dec(x_916);
x_919 = lean_st_ref_get(x_4, x_917);
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
lean_dec(x_919);
x_922 = lean_ctor_get(x_920, 3);
lean_inc(x_922);
lean_dec(x_920);
x_923 = lean_ctor_get(x_7, 1);
lean_inc(x_923);
x_924 = lean_ctor_get(x_7, 2);
lean_inc(x_924);
x_925 = lean_environment_main_module(x_918);
x_926 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_913);
lean_ctor_set(x_926, 2, x_923);
lean_ctor_set(x_926, 3, x_924);
lean_inc(x_1);
x_927 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_926, x_922);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; uint8_t x_933; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = lean_st_ref_take(x_4, x_921);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_933 = !lean_is_exclusive(x_931);
if (x_933 == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; 
x_934 = lean_ctor_get(x_931, 3);
lean_dec(x_934);
lean_ctor_set(x_931, 3, x_929);
x_935 = lean_st_ref_set(x_4, x_931, x_932);
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
lean_dec(x_935);
x_10 = x_928;
x_11 = x_936;
goto block_36;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_937 = lean_ctor_get(x_931, 0);
x_938 = lean_ctor_get(x_931, 1);
x_939 = lean_ctor_get(x_931, 2);
x_940 = lean_ctor_get(x_931, 4);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_dec(x_931);
x_941 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_941, 0, x_937);
lean_ctor_set(x_941, 1, x_938);
lean_ctor_set(x_941, 2, x_939);
lean_ctor_set(x_941, 3, x_929);
lean_ctor_set(x_941, 4, x_940);
x_942 = lean_st_ref_set(x_4, x_941, x_932);
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
lean_dec(x_942);
x_10 = x_928;
x_11 = x_943;
goto block_36;
}
}
else
{
lean_object* x_944; 
lean_dec(x_2);
lean_dec(x_1);
x_944 = lean_ctor_get(x_927, 0);
lean_inc(x_944);
lean_dec(x_927);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; uint8_t x_950; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
x_947 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_947, 0, x_946);
x_948 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_948, 0, x_947);
x_949 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_945, x_948, x_3, x_4, x_5, x_6, x_7, x_8, x_921);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_945);
x_950 = !lean_is_exclusive(x_949);
if (x_950 == 0)
{
return x_949;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_949, 0);
x_952 = lean_ctor_get(x_949, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_949);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
else
{
lean_object* x_954; uint8_t x_955; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_954 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_921);
x_955 = !lean_is_exclusive(x_954);
if (x_955 == 0)
{
return x_954;
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_956 = lean_ctor_get(x_954, 0);
x_957 = lean_ctor_get(x_954, 1);
lean_inc(x_957);
lean_inc(x_956);
lean_dec(x_954);
x_958 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set(x_958, 1, x_957);
return x_958;
}
}
}
}
else
{
lean_object* x_959; uint8_t x_960; uint8_t x_1228; uint8_t x_1229; 
x_959 = l_Lean_Syntax_getArg(x_910, x_135);
lean_inc(x_959);
x_1228 = l_Lean_Syntax_isOfKind(x_959, x_902);
if (x_1228 == 0)
{
uint8_t x_1454; 
x_1454 = 0;
x_1229 = x_1454;
goto block_1453;
}
else
{
lean_object* x_1455; lean_object* x_1456; uint8_t x_1457; 
x_1455 = l_Lean_Syntax_getArgs(x_959);
x_1456 = lean_array_get_size(x_1455);
lean_dec(x_1455);
x_1457 = lean_nat_dec_eq(x_1456, x_135);
lean_dec(x_1456);
x_1229 = x_1457;
goto block_1453;
}
block_1227:
{
if (x_960 == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_dec(x_910);
lean_dec(x_234);
x_961 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = lean_st_ref_get(x_8, x_963);
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_967 = lean_ctor_get(x_965, 0);
lean_inc(x_967);
lean_dec(x_965);
x_968 = lean_st_ref_get(x_4, x_966);
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
lean_dec(x_968);
x_971 = lean_ctor_get(x_969, 3);
lean_inc(x_971);
lean_dec(x_969);
x_972 = lean_ctor_get(x_7, 1);
lean_inc(x_972);
x_973 = lean_ctor_get(x_7, 2);
lean_inc(x_973);
x_974 = lean_environment_main_module(x_967);
x_975 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_975, 1, x_962);
lean_ctor_set(x_975, 2, x_972);
lean_ctor_set(x_975, 3, x_973);
lean_inc(x_1);
x_976 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_975, x_971);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; uint8_t x_982; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec(x_976);
x_979 = lean_st_ref_take(x_4, x_970);
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_979, 1);
lean_inc(x_981);
lean_dec(x_979);
x_982 = !lean_is_exclusive(x_980);
if (x_982 == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_983 = lean_ctor_get(x_980, 3);
lean_dec(x_983);
lean_ctor_set(x_980, 3, x_978);
x_984 = lean_st_ref_set(x_4, x_980, x_981);
x_985 = lean_ctor_get(x_984, 1);
lean_inc(x_985);
lean_dec(x_984);
x_10 = x_977;
x_11 = x_985;
goto block_36;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_986 = lean_ctor_get(x_980, 0);
x_987 = lean_ctor_get(x_980, 1);
x_988 = lean_ctor_get(x_980, 2);
x_989 = lean_ctor_get(x_980, 4);
lean_inc(x_989);
lean_inc(x_988);
lean_inc(x_987);
lean_inc(x_986);
lean_dec(x_980);
x_990 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_990, 0, x_986);
lean_ctor_set(x_990, 1, x_987);
lean_ctor_set(x_990, 2, x_988);
lean_ctor_set(x_990, 3, x_978);
lean_ctor_set(x_990, 4, x_989);
x_991 = lean_st_ref_set(x_4, x_990, x_981);
x_992 = lean_ctor_get(x_991, 1);
lean_inc(x_992);
lean_dec(x_991);
x_10 = x_977;
x_11 = x_992;
goto block_36;
}
}
else
{
lean_object* x_993; 
lean_dec(x_2);
lean_dec(x_1);
x_993 = lean_ctor_get(x_976, 0);
lean_inc(x_993);
lean_dec(x_976);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
x_996 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_996, 0, x_995);
x_997 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_997, 0, x_996);
x_998 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_994, x_997, x_3, x_4, x_5, x_6, x_7, x_8, x_970);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_994);
x_999 = !lean_is_exclusive(x_998);
if (x_999 == 0)
{
return x_998;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_998, 0);
x_1001 = lean_ctor_get(x_998, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_998);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
else
{
lean_object* x_1003; uint8_t x_1004; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1003 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_970);
x_1004 = !lean_is_exclusive(x_1003);
if (x_1004 == 0)
{
return x_1003;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1005 = lean_ctor_get(x_1003, 0);
x_1006 = lean_ctor_get(x_1003, 1);
lean_inc(x_1006);
lean_inc(x_1005);
lean_dec(x_1003);
x_1007 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1007, 0, x_1005);
lean_ctor_set(x_1007, 1, x_1006);
return x_1007;
}
}
}
}
else
{
lean_object* x_1008; uint8_t x_1009; uint8_t x_1222; 
x_1008 = l_Lean_Syntax_getArg(x_910, x_85);
lean_dec(x_910);
lean_inc(x_1008);
x_1222 = l_Lean_Syntax_isOfKind(x_1008, x_902);
if (x_1222 == 0)
{
uint8_t x_1223; 
x_1223 = 0;
x_1009 = x_1223;
goto block_1221;
}
else
{
lean_object* x_1224; lean_object* x_1225; uint8_t x_1226; 
x_1224 = l_Lean_Syntax_getArgs(x_1008);
x_1225 = lean_array_get_size(x_1224);
lean_dec(x_1224);
x_1226 = lean_nat_dec_eq(x_1225, x_85);
lean_dec(x_1225);
x_1009 = x_1226;
goto block_1221;
}
block_1221:
{
if (x_1009 == 0)
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_1008);
lean_dec(x_234);
x_1010 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
x_1013 = lean_st_ref_get(x_8, x_1012);
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1013, 1);
lean_inc(x_1015);
lean_dec(x_1013);
x_1016 = lean_ctor_get(x_1014, 0);
lean_inc(x_1016);
lean_dec(x_1014);
x_1017 = lean_st_ref_get(x_4, x_1015);
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = lean_ctor_get(x_1018, 3);
lean_inc(x_1020);
lean_dec(x_1018);
x_1021 = lean_ctor_get(x_7, 1);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_7, 2);
lean_inc(x_1022);
x_1023 = lean_environment_main_module(x_1016);
x_1024 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_1011);
lean_ctor_set(x_1024, 2, x_1021);
lean_ctor_set(x_1024, 3, x_1022);
lean_inc(x_1);
x_1025 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1024, x_1020);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; uint8_t x_1031; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
lean_dec(x_1025);
x_1028 = lean_st_ref_take(x_4, x_1019);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
lean_dec(x_1028);
x_1031 = !lean_is_exclusive(x_1029);
if (x_1031 == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_1029, 3);
lean_dec(x_1032);
lean_ctor_set(x_1029, 3, x_1027);
x_1033 = lean_st_ref_set(x_4, x_1029, x_1030);
x_1034 = lean_ctor_get(x_1033, 1);
lean_inc(x_1034);
lean_dec(x_1033);
x_10 = x_1026;
x_11 = x_1034;
goto block_36;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1035 = lean_ctor_get(x_1029, 0);
x_1036 = lean_ctor_get(x_1029, 1);
x_1037 = lean_ctor_get(x_1029, 2);
x_1038 = lean_ctor_get(x_1029, 4);
lean_inc(x_1038);
lean_inc(x_1037);
lean_inc(x_1036);
lean_inc(x_1035);
lean_dec(x_1029);
x_1039 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1039, 0, x_1035);
lean_ctor_set(x_1039, 1, x_1036);
lean_ctor_set(x_1039, 2, x_1037);
lean_ctor_set(x_1039, 3, x_1027);
lean_ctor_set(x_1039, 4, x_1038);
x_1040 = lean_st_ref_set(x_4, x_1039, x_1030);
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
lean_dec(x_1040);
x_10 = x_1026;
x_11 = x_1041;
goto block_36;
}
}
else
{
lean_object* x_1042; 
lean_dec(x_2);
lean_dec(x_1);
x_1042 = lean_ctor_get(x_1025, 0);
lean_inc(x_1042);
lean_dec(x_1025);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; uint8_t x_1048; 
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1042, 1);
lean_inc(x_1044);
lean_dec(x_1042);
x_1045 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1045, 0, x_1044);
x_1046 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1046, 0, x_1045);
x_1047 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1043, x_1046, x_3, x_4, x_5, x_6, x_7, x_8, x_1019);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1043);
x_1048 = !lean_is_exclusive(x_1047);
if (x_1048 == 0)
{
return x_1047;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1049 = lean_ctor_get(x_1047, 0);
x_1050 = lean_ctor_get(x_1047, 1);
lean_inc(x_1050);
lean_inc(x_1049);
lean_dec(x_1047);
x_1051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1051, 0, x_1049);
lean_ctor_set(x_1051, 1, x_1050);
return x_1051;
}
}
else
{
lean_object* x_1052; uint8_t x_1053; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1052 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1019);
x_1053 = !lean_is_exclusive(x_1052);
if (x_1053 == 0)
{
return x_1052;
}
else
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1054 = lean_ctor_get(x_1052, 0);
x_1055 = lean_ctor_get(x_1052, 1);
lean_inc(x_1055);
lean_inc(x_1054);
lean_dec(x_1052);
x_1056 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1056, 0, x_1054);
lean_ctor_set(x_1056, 1, x_1055);
return x_1056;
}
}
}
}
else
{
lean_object* x_1057; uint8_t x_1058; lean_object* x_1214; uint8_t x_1215; 
x_1057 = l_Lean_Syntax_getArg(x_1008, x_135);
lean_dec(x_1008);
x_1214 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_1057);
x_1215 = l_Lean_Syntax_isOfKind(x_1057, x_1214);
if (x_1215 == 0)
{
uint8_t x_1216; 
x_1216 = 0;
x_1058 = x_1216;
goto block_1213;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; uint8_t x_1220; 
x_1217 = l_Lean_Syntax_getArgs(x_1057);
x_1218 = lean_array_get_size(x_1217);
lean_dec(x_1217);
x_1219 = lean_unsigned_to_nat(3u);
x_1220 = lean_nat_dec_eq(x_1218, x_1219);
lean_dec(x_1218);
x_1058 = x_1220;
goto block_1213;
}
block_1213:
{
if (x_1058 == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_1057);
lean_dec(x_234);
x_1059 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1059, 1);
lean_inc(x_1061);
lean_dec(x_1059);
x_1062 = lean_st_ref_get(x_8, x_1061);
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec(x_1062);
x_1065 = lean_ctor_get(x_1063, 0);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_st_ref_get(x_4, x_1064);
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
lean_dec(x_1066);
x_1069 = lean_ctor_get(x_1067, 3);
lean_inc(x_1069);
lean_dec(x_1067);
x_1070 = lean_ctor_get(x_7, 1);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_7, 2);
lean_inc(x_1071);
x_1072 = lean_environment_main_module(x_1065);
x_1073 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1073, 0, x_1072);
lean_ctor_set(x_1073, 1, x_1060);
lean_ctor_set(x_1073, 2, x_1070);
lean_ctor_set(x_1073, 3, x_1071);
lean_inc(x_1);
x_1074 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1073, x_1069);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
lean_dec(x_1074);
x_1077 = lean_st_ref_take(x_4, x_1068);
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
x_1080 = !lean_is_exclusive(x_1078);
if (x_1080 == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1078, 3);
lean_dec(x_1081);
lean_ctor_set(x_1078, 3, x_1076);
x_1082 = lean_st_ref_set(x_4, x_1078, x_1079);
x_1083 = lean_ctor_get(x_1082, 1);
lean_inc(x_1083);
lean_dec(x_1082);
x_10 = x_1075;
x_11 = x_1083;
goto block_36;
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1084 = lean_ctor_get(x_1078, 0);
x_1085 = lean_ctor_get(x_1078, 1);
x_1086 = lean_ctor_get(x_1078, 2);
x_1087 = lean_ctor_get(x_1078, 4);
lean_inc(x_1087);
lean_inc(x_1086);
lean_inc(x_1085);
lean_inc(x_1084);
lean_dec(x_1078);
x_1088 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1088, 0, x_1084);
lean_ctor_set(x_1088, 1, x_1085);
lean_ctor_set(x_1088, 2, x_1086);
lean_ctor_set(x_1088, 3, x_1076);
lean_ctor_set(x_1088, 4, x_1087);
x_1089 = lean_st_ref_set(x_4, x_1088, x_1079);
x_1090 = lean_ctor_get(x_1089, 1);
lean_inc(x_1090);
lean_dec(x_1089);
x_10 = x_1075;
x_11 = x_1090;
goto block_36;
}
}
else
{
lean_object* x_1091; 
lean_dec(x_2);
lean_dec(x_1);
x_1091 = lean_ctor_get(x_1074, 0);
lean_inc(x_1091);
lean_dec(x_1074);
if (lean_obj_tag(x_1091) == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; 
x_1092 = lean_ctor_get(x_1091, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1091, 1);
lean_inc(x_1093);
lean_dec(x_1091);
x_1094 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1094, 0, x_1093);
x_1095 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1095, 0, x_1094);
x_1096 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1092, x_1095, x_3, x_4, x_5, x_6, x_7, x_8, x_1068);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1092);
x_1097 = !lean_is_exclusive(x_1096);
if (x_1097 == 0)
{
return x_1096;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1098 = lean_ctor_get(x_1096, 0);
x_1099 = lean_ctor_get(x_1096, 1);
lean_inc(x_1099);
lean_inc(x_1098);
lean_dec(x_1096);
x_1100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1100, 0, x_1098);
lean_ctor_set(x_1100, 1, x_1099);
return x_1100;
}
}
else
{
lean_object* x_1101; uint8_t x_1102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1101 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1068);
x_1102 = !lean_is_exclusive(x_1101);
if (x_1102 == 0)
{
return x_1101;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1103 = lean_ctor_get(x_1101, 0);
x_1104 = lean_ctor_get(x_1101, 1);
lean_inc(x_1104);
lean_inc(x_1103);
lean_dec(x_1101);
x_1105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1105, 0, x_1103);
lean_ctor_set(x_1105, 1, x_1104);
return x_1105;
}
}
}
}
else
{
lean_object* x_1106; uint8_t x_1107; uint8_t x_1208; 
x_1106 = l_Lean_Syntax_getArg(x_1057, x_135);
lean_inc(x_1106);
x_1208 = l_Lean_Syntax_isOfKind(x_1106, x_902);
if (x_1208 == 0)
{
uint8_t x_1209; 
x_1209 = 0;
x_1107 = x_1209;
goto block_1207;
}
else
{
lean_object* x_1210; lean_object* x_1211; uint8_t x_1212; 
x_1210 = l_Lean_Syntax_getArgs(x_1106);
x_1211 = lean_array_get_size(x_1210);
lean_dec(x_1210);
x_1212 = lean_nat_dec_eq(x_1211, x_85);
lean_dec(x_1211);
x_1107 = x_1212;
goto block_1207;
}
block_1207:
{
if (x_1107 == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_1106);
lean_dec(x_1057);
lean_dec(x_234);
x_1108 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
lean_dec(x_1108);
x_1111 = lean_st_ref_get(x_8, x_1110);
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
lean_dec(x_1111);
x_1114 = lean_ctor_get(x_1112, 0);
lean_inc(x_1114);
lean_dec(x_1112);
x_1115 = lean_st_ref_get(x_4, x_1113);
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
x_1118 = lean_ctor_get(x_1116, 3);
lean_inc(x_1118);
lean_dec(x_1116);
x_1119 = lean_ctor_get(x_7, 1);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_7, 2);
lean_inc(x_1120);
x_1121 = lean_environment_main_module(x_1114);
x_1122 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1122, 0, x_1121);
lean_ctor_set(x_1122, 1, x_1109);
lean_ctor_set(x_1122, 2, x_1119);
lean_ctor_set(x_1122, 3, x_1120);
lean_inc(x_1);
x_1123 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1122, x_1118);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; 
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1123, 1);
lean_inc(x_1125);
lean_dec(x_1123);
x_1126 = lean_st_ref_take(x_4, x_1117);
x_1127 = lean_ctor_get(x_1126, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1126, 1);
lean_inc(x_1128);
lean_dec(x_1126);
x_1129 = !lean_is_exclusive(x_1127);
if (x_1129 == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1127, 3);
lean_dec(x_1130);
lean_ctor_set(x_1127, 3, x_1125);
x_1131 = lean_st_ref_set(x_4, x_1127, x_1128);
x_1132 = lean_ctor_get(x_1131, 1);
lean_inc(x_1132);
lean_dec(x_1131);
x_10 = x_1124;
x_11 = x_1132;
goto block_36;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1133 = lean_ctor_get(x_1127, 0);
x_1134 = lean_ctor_get(x_1127, 1);
x_1135 = lean_ctor_get(x_1127, 2);
x_1136 = lean_ctor_get(x_1127, 4);
lean_inc(x_1136);
lean_inc(x_1135);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_1127);
x_1137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1137, 0, x_1133);
lean_ctor_set(x_1137, 1, x_1134);
lean_ctor_set(x_1137, 2, x_1135);
lean_ctor_set(x_1137, 3, x_1125);
lean_ctor_set(x_1137, 4, x_1136);
x_1138 = lean_st_ref_set(x_4, x_1137, x_1128);
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
lean_dec(x_1138);
x_10 = x_1124;
x_11 = x_1139;
goto block_36;
}
}
else
{
lean_object* x_1140; 
lean_dec(x_2);
lean_dec(x_1);
x_1140 = lean_ctor_get(x_1123, 0);
lean_inc(x_1140);
lean_dec(x_1123);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; uint8_t x_1146; 
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec(x_1140);
x_1143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1143, 0, x_1142);
x_1144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1144, 0, x_1143);
x_1145 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1141, x_1144, x_3, x_4, x_5, x_6, x_7, x_8, x_1117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1141);
x_1146 = !lean_is_exclusive(x_1145);
if (x_1146 == 0)
{
return x_1145;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1147 = lean_ctor_get(x_1145, 0);
x_1148 = lean_ctor_get(x_1145, 1);
lean_inc(x_1148);
lean_inc(x_1147);
lean_dec(x_1145);
x_1149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set(x_1149, 1, x_1148);
return x_1149;
}
}
else
{
lean_object* x_1150; uint8_t x_1151; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1150 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1117);
x_1151 = !lean_is_exclusive(x_1150);
if (x_1151 == 0)
{
return x_1150;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_1150, 0);
x_1153 = lean_ctor_get(x_1150, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_1150);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
}
else
{
lean_object* x_1155; lean_object* x_1156; uint8_t x_1157; 
x_1155 = l_Lean_Syntax_getArg(x_1106, x_135);
lean_dec(x_1106);
x_1156 = l_Lean_identKind___closed__2;
lean_inc(x_1155);
x_1157 = l_Lean_Syntax_isOfKind(x_1155, x_1156);
if (x_1157 == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
lean_dec(x_1155);
lean_dec(x_1057);
lean_dec(x_234);
x_1158 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
lean_dec(x_1158);
x_1161 = lean_st_ref_get(x_8, x_1160);
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
lean_dec(x_1161);
x_1164 = lean_ctor_get(x_1162, 0);
lean_inc(x_1164);
lean_dec(x_1162);
x_1165 = lean_st_ref_get(x_4, x_1163);
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = lean_ctor_get(x_1166, 3);
lean_inc(x_1168);
lean_dec(x_1166);
x_1169 = lean_ctor_get(x_7, 1);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_7, 2);
lean_inc(x_1170);
x_1171 = lean_environment_main_module(x_1164);
x_1172 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1172, 0, x_1171);
lean_ctor_set(x_1172, 1, x_1159);
lean_ctor_set(x_1172, 2, x_1169);
lean_ctor_set(x_1172, 3, x_1170);
lean_inc(x_1);
x_1173 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1172, x_1168);
if (lean_obj_tag(x_1173) == 0)
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; 
x_1174 = lean_ctor_get(x_1173, 0);
lean_inc(x_1174);
x_1175 = lean_ctor_get(x_1173, 1);
lean_inc(x_1175);
lean_dec(x_1173);
x_1176 = lean_st_ref_take(x_4, x_1167);
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1176, 1);
lean_inc(x_1178);
lean_dec(x_1176);
x_1179 = !lean_is_exclusive(x_1177);
if (x_1179 == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1177, 3);
lean_dec(x_1180);
lean_ctor_set(x_1177, 3, x_1175);
x_1181 = lean_st_ref_set(x_4, x_1177, x_1178);
x_1182 = lean_ctor_get(x_1181, 1);
lean_inc(x_1182);
lean_dec(x_1181);
x_10 = x_1174;
x_11 = x_1182;
goto block_36;
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1183 = lean_ctor_get(x_1177, 0);
x_1184 = lean_ctor_get(x_1177, 1);
x_1185 = lean_ctor_get(x_1177, 2);
x_1186 = lean_ctor_get(x_1177, 4);
lean_inc(x_1186);
lean_inc(x_1185);
lean_inc(x_1184);
lean_inc(x_1183);
lean_dec(x_1177);
x_1187 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1187, 0, x_1183);
lean_ctor_set(x_1187, 1, x_1184);
lean_ctor_set(x_1187, 2, x_1185);
lean_ctor_set(x_1187, 3, x_1175);
lean_ctor_set(x_1187, 4, x_1186);
x_1188 = lean_st_ref_set(x_4, x_1187, x_1178);
x_1189 = lean_ctor_get(x_1188, 1);
lean_inc(x_1189);
lean_dec(x_1188);
x_10 = x_1174;
x_11 = x_1189;
goto block_36;
}
}
else
{
lean_object* x_1190; 
lean_dec(x_2);
lean_dec(x_1);
x_1190 = lean_ctor_get(x_1173, 0);
lean_inc(x_1190);
lean_dec(x_1173);
if (lean_obj_tag(x_1190) == 0)
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; 
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1190, 1);
lean_inc(x_1192);
lean_dec(x_1190);
x_1193 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1193, 0, x_1192);
x_1194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1194, 0, x_1193);
x_1195 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1191, x_1194, x_3, x_4, x_5, x_6, x_7, x_8, x_1167);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1191);
x_1196 = !lean_is_exclusive(x_1195);
if (x_1196 == 0)
{
return x_1195;
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_1195, 0);
x_1198 = lean_ctor_get(x_1195, 1);
lean_inc(x_1198);
lean_inc(x_1197);
lean_dec(x_1195);
x_1199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1199, 0, x_1197);
lean_ctor_set(x_1199, 1, x_1198);
return x_1199;
}
}
else
{
lean_object* x_1200; uint8_t x_1201; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1200 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1167);
x_1201 = !lean_is_exclusive(x_1200);
if (x_1201 == 0)
{
return x_1200;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1202 = lean_ctor_get(x_1200, 0);
x_1203 = lean_ctor_get(x_1200, 1);
lean_inc(x_1203);
lean_inc(x_1202);
lean_dec(x_1200);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1202);
lean_ctor_set(x_1204, 1, x_1203);
return x_1204;
}
}
}
}
else
{
lean_object* x_1205; lean_object* x_1206; 
x_1205 = l_Lean_Syntax_getArg(x_1057, x_235);
lean_dec(x_1057);
x_1206 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_234, x_1155, x_1205, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1206;
}
}
}
}
}
}
}
}
}
block_1453:
{
if (x_1229 == 0)
{
if (x_1228 == 0)
{
uint8_t x_1230; 
lean_dec(x_959);
x_1230 = 0;
x_960 = x_1230;
goto block_1227;
}
else
{
lean_object* x_1231; lean_object* x_1232; uint8_t x_1233; 
x_1231 = l_Lean_Syntax_getArgs(x_959);
lean_dec(x_959);
x_1232 = lean_array_get_size(x_1231);
lean_dec(x_1231);
x_1233 = lean_nat_dec_eq(x_1232, x_85);
lean_dec(x_1232);
x_960 = x_1233;
goto block_1227;
}
}
else
{
lean_object* x_1234; uint8_t x_1235; uint8_t x_1448; 
lean_dec(x_959);
x_1234 = l_Lean_Syntax_getArg(x_910, x_85);
lean_dec(x_910);
lean_inc(x_1234);
x_1448 = l_Lean_Syntax_isOfKind(x_1234, x_902);
if (x_1448 == 0)
{
uint8_t x_1449; 
x_1449 = 0;
x_1235 = x_1449;
goto block_1447;
}
else
{
lean_object* x_1450; lean_object* x_1451; uint8_t x_1452; 
x_1450 = l_Lean_Syntax_getArgs(x_1234);
x_1451 = lean_array_get_size(x_1450);
lean_dec(x_1450);
x_1452 = lean_nat_dec_eq(x_1451, x_85);
lean_dec(x_1451);
x_1235 = x_1452;
goto block_1447;
}
block_1447:
{
if (x_1235 == 0)
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1234);
lean_dec(x_234);
x_1236 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
lean_dec(x_1236);
x_1239 = lean_st_ref_get(x_8, x_1238);
x_1240 = lean_ctor_get(x_1239, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1239, 1);
lean_inc(x_1241);
lean_dec(x_1239);
x_1242 = lean_ctor_get(x_1240, 0);
lean_inc(x_1242);
lean_dec(x_1240);
x_1243 = lean_st_ref_get(x_4, x_1241);
x_1244 = lean_ctor_get(x_1243, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1243, 1);
lean_inc(x_1245);
lean_dec(x_1243);
x_1246 = lean_ctor_get(x_1244, 3);
lean_inc(x_1246);
lean_dec(x_1244);
x_1247 = lean_ctor_get(x_7, 1);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_7, 2);
lean_inc(x_1248);
x_1249 = lean_environment_main_module(x_1242);
x_1250 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1237);
lean_ctor_set(x_1250, 2, x_1247);
lean_ctor_set(x_1250, 3, x_1248);
lean_inc(x_1);
x_1251 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1250, x_1246);
if (lean_obj_tag(x_1251) == 0)
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; uint8_t x_1257; 
x_1252 = lean_ctor_get(x_1251, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1251, 1);
lean_inc(x_1253);
lean_dec(x_1251);
x_1254 = lean_st_ref_take(x_4, x_1245);
x_1255 = lean_ctor_get(x_1254, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1254, 1);
lean_inc(x_1256);
lean_dec(x_1254);
x_1257 = !lean_is_exclusive(x_1255);
if (x_1257 == 0)
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1258 = lean_ctor_get(x_1255, 3);
lean_dec(x_1258);
lean_ctor_set(x_1255, 3, x_1253);
x_1259 = lean_st_ref_set(x_4, x_1255, x_1256);
x_1260 = lean_ctor_get(x_1259, 1);
lean_inc(x_1260);
lean_dec(x_1259);
x_10 = x_1252;
x_11 = x_1260;
goto block_36;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1261 = lean_ctor_get(x_1255, 0);
x_1262 = lean_ctor_get(x_1255, 1);
x_1263 = lean_ctor_get(x_1255, 2);
x_1264 = lean_ctor_get(x_1255, 4);
lean_inc(x_1264);
lean_inc(x_1263);
lean_inc(x_1262);
lean_inc(x_1261);
lean_dec(x_1255);
x_1265 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1265, 0, x_1261);
lean_ctor_set(x_1265, 1, x_1262);
lean_ctor_set(x_1265, 2, x_1263);
lean_ctor_set(x_1265, 3, x_1253);
lean_ctor_set(x_1265, 4, x_1264);
x_1266 = lean_st_ref_set(x_4, x_1265, x_1256);
x_1267 = lean_ctor_get(x_1266, 1);
lean_inc(x_1267);
lean_dec(x_1266);
x_10 = x_1252;
x_11 = x_1267;
goto block_36;
}
}
else
{
lean_object* x_1268; 
lean_dec(x_2);
lean_dec(x_1);
x_1268 = lean_ctor_get(x_1251, 0);
lean_inc(x_1268);
lean_dec(x_1251);
if (lean_obj_tag(x_1268) == 0)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; uint8_t x_1274; 
x_1269 = lean_ctor_get(x_1268, 0);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1268, 1);
lean_inc(x_1270);
lean_dec(x_1268);
x_1271 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1271, 0, x_1270);
x_1272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1272, 0, x_1271);
x_1273 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1269, x_1272, x_3, x_4, x_5, x_6, x_7, x_8, x_1245);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1269);
x_1274 = !lean_is_exclusive(x_1273);
if (x_1274 == 0)
{
return x_1273;
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1275 = lean_ctor_get(x_1273, 0);
x_1276 = lean_ctor_get(x_1273, 1);
lean_inc(x_1276);
lean_inc(x_1275);
lean_dec(x_1273);
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1275);
lean_ctor_set(x_1277, 1, x_1276);
return x_1277;
}
}
else
{
lean_object* x_1278; uint8_t x_1279; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1278 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1245);
x_1279 = !lean_is_exclusive(x_1278);
if (x_1279 == 0)
{
return x_1278;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1280 = lean_ctor_get(x_1278, 0);
x_1281 = lean_ctor_get(x_1278, 1);
lean_inc(x_1281);
lean_inc(x_1280);
lean_dec(x_1278);
x_1282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1282, 0, x_1280);
lean_ctor_set(x_1282, 1, x_1281);
return x_1282;
}
}
}
}
else
{
lean_object* x_1283; uint8_t x_1284; lean_object* x_1440; uint8_t x_1441; 
x_1283 = l_Lean_Syntax_getArg(x_1234, x_135);
lean_dec(x_1234);
x_1440 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_1283);
x_1441 = l_Lean_Syntax_isOfKind(x_1283, x_1440);
if (x_1441 == 0)
{
uint8_t x_1442; 
x_1442 = 0;
x_1284 = x_1442;
goto block_1439;
}
else
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; 
x_1443 = l_Lean_Syntax_getArgs(x_1283);
x_1444 = lean_array_get_size(x_1443);
lean_dec(x_1443);
x_1445 = lean_unsigned_to_nat(3u);
x_1446 = lean_nat_dec_eq(x_1444, x_1445);
lean_dec(x_1444);
x_1284 = x_1446;
goto block_1439;
}
block_1439:
{
if (x_1284 == 0)
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
lean_dec(x_1283);
lean_dec(x_234);
x_1285 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1285, 1);
lean_inc(x_1287);
lean_dec(x_1285);
x_1288 = lean_st_ref_get(x_8, x_1287);
x_1289 = lean_ctor_get(x_1288, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1288, 1);
lean_inc(x_1290);
lean_dec(x_1288);
x_1291 = lean_ctor_get(x_1289, 0);
lean_inc(x_1291);
lean_dec(x_1289);
x_1292 = lean_st_ref_get(x_4, x_1290);
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1292, 1);
lean_inc(x_1294);
lean_dec(x_1292);
x_1295 = lean_ctor_get(x_1293, 3);
lean_inc(x_1295);
lean_dec(x_1293);
x_1296 = lean_ctor_get(x_7, 1);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_7, 2);
lean_inc(x_1297);
x_1298 = lean_environment_main_module(x_1291);
x_1299 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1299, 0, x_1298);
lean_ctor_set(x_1299, 1, x_1286);
lean_ctor_set(x_1299, 2, x_1296);
lean_ctor_set(x_1299, 3, x_1297);
lean_inc(x_1);
x_1300 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1299, x_1295);
if (lean_obj_tag(x_1300) == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; uint8_t x_1306; 
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
lean_dec(x_1300);
x_1303 = lean_st_ref_take(x_4, x_1294);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
lean_dec(x_1303);
x_1306 = !lean_is_exclusive(x_1304);
if (x_1306 == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
x_1307 = lean_ctor_get(x_1304, 3);
lean_dec(x_1307);
lean_ctor_set(x_1304, 3, x_1302);
x_1308 = lean_st_ref_set(x_4, x_1304, x_1305);
x_1309 = lean_ctor_get(x_1308, 1);
lean_inc(x_1309);
lean_dec(x_1308);
x_10 = x_1301;
x_11 = x_1309;
goto block_36;
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1310 = lean_ctor_get(x_1304, 0);
x_1311 = lean_ctor_get(x_1304, 1);
x_1312 = lean_ctor_get(x_1304, 2);
x_1313 = lean_ctor_get(x_1304, 4);
lean_inc(x_1313);
lean_inc(x_1312);
lean_inc(x_1311);
lean_inc(x_1310);
lean_dec(x_1304);
x_1314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1314, 0, x_1310);
lean_ctor_set(x_1314, 1, x_1311);
lean_ctor_set(x_1314, 2, x_1312);
lean_ctor_set(x_1314, 3, x_1302);
lean_ctor_set(x_1314, 4, x_1313);
x_1315 = lean_st_ref_set(x_4, x_1314, x_1305);
x_1316 = lean_ctor_get(x_1315, 1);
lean_inc(x_1316);
lean_dec(x_1315);
x_10 = x_1301;
x_11 = x_1316;
goto block_36;
}
}
else
{
lean_object* x_1317; 
lean_dec(x_2);
lean_dec(x_1);
x_1317 = lean_ctor_get(x_1300, 0);
lean_inc(x_1317);
lean_dec(x_1300);
if (lean_obj_tag(x_1317) == 0)
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; uint8_t x_1323; 
x_1318 = lean_ctor_get(x_1317, 0);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1317, 1);
lean_inc(x_1319);
lean_dec(x_1317);
x_1320 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1320, 0, x_1319);
x_1321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1321, 0, x_1320);
x_1322 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1318, x_1321, x_3, x_4, x_5, x_6, x_7, x_8, x_1294);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1318);
x_1323 = !lean_is_exclusive(x_1322);
if (x_1323 == 0)
{
return x_1322;
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
x_1324 = lean_ctor_get(x_1322, 0);
x_1325 = lean_ctor_get(x_1322, 1);
lean_inc(x_1325);
lean_inc(x_1324);
lean_dec(x_1322);
x_1326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1326, 0, x_1324);
lean_ctor_set(x_1326, 1, x_1325);
return x_1326;
}
}
else
{
lean_object* x_1327; uint8_t x_1328; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1327 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1294);
x_1328 = !lean_is_exclusive(x_1327);
if (x_1328 == 0)
{
return x_1327;
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
x_1329 = lean_ctor_get(x_1327, 0);
x_1330 = lean_ctor_get(x_1327, 1);
lean_inc(x_1330);
lean_inc(x_1329);
lean_dec(x_1327);
x_1331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1331, 0, x_1329);
lean_ctor_set(x_1331, 1, x_1330);
return x_1331;
}
}
}
}
else
{
lean_object* x_1332; uint8_t x_1333; uint8_t x_1434; 
x_1332 = l_Lean_Syntax_getArg(x_1283, x_135);
lean_inc(x_1332);
x_1434 = l_Lean_Syntax_isOfKind(x_1332, x_902);
if (x_1434 == 0)
{
uint8_t x_1435; 
x_1435 = 0;
x_1333 = x_1435;
goto block_1433;
}
else
{
lean_object* x_1436; lean_object* x_1437; uint8_t x_1438; 
x_1436 = l_Lean_Syntax_getArgs(x_1332);
x_1437 = lean_array_get_size(x_1436);
lean_dec(x_1436);
x_1438 = lean_nat_dec_eq(x_1437, x_85);
lean_dec(x_1437);
x_1333 = x_1438;
goto block_1433;
}
block_1433:
{
if (x_1333 == 0)
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; 
lean_dec(x_1332);
lean_dec(x_1283);
lean_dec(x_234);
x_1334 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
lean_dec(x_1334);
x_1337 = lean_st_ref_get(x_8, x_1336);
x_1338 = lean_ctor_get(x_1337, 0);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1337, 1);
lean_inc(x_1339);
lean_dec(x_1337);
x_1340 = lean_ctor_get(x_1338, 0);
lean_inc(x_1340);
lean_dec(x_1338);
x_1341 = lean_st_ref_get(x_4, x_1339);
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1341, 1);
lean_inc(x_1343);
lean_dec(x_1341);
x_1344 = lean_ctor_get(x_1342, 3);
lean_inc(x_1344);
lean_dec(x_1342);
x_1345 = lean_ctor_get(x_7, 1);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_7, 2);
lean_inc(x_1346);
x_1347 = lean_environment_main_module(x_1340);
x_1348 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_1335);
lean_ctor_set(x_1348, 2, x_1345);
lean_ctor_set(x_1348, 3, x_1346);
lean_inc(x_1);
x_1349 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1348, x_1344);
if (lean_obj_tag(x_1349) == 0)
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; uint8_t x_1355; 
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec(x_1349);
x_1352 = lean_st_ref_take(x_4, x_1343);
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
lean_dec(x_1352);
x_1355 = !lean_is_exclusive(x_1353);
if (x_1355 == 0)
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1356 = lean_ctor_get(x_1353, 3);
lean_dec(x_1356);
lean_ctor_set(x_1353, 3, x_1351);
x_1357 = lean_st_ref_set(x_4, x_1353, x_1354);
x_1358 = lean_ctor_get(x_1357, 1);
lean_inc(x_1358);
lean_dec(x_1357);
x_10 = x_1350;
x_11 = x_1358;
goto block_36;
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1359 = lean_ctor_get(x_1353, 0);
x_1360 = lean_ctor_get(x_1353, 1);
x_1361 = lean_ctor_get(x_1353, 2);
x_1362 = lean_ctor_get(x_1353, 4);
lean_inc(x_1362);
lean_inc(x_1361);
lean_inc(x_1360);
lean_inc(x_1359);
lean_dec(x_1353);
x_1363 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1363, 0, x_1359);
lean_ctor_set(x_1363, 1, x_1360);
lean_ctor_set(x_1363, 2, x_1361);
lean_ctor_set(x_1363, 3, x_1351);
lean_ctor_set(x_1363, 4, x_1362);
x_1364 = lean_st_ref_set(x_4, x_1363, x_1354);
x_1365 = lean_ctor_get(x_1364, 1);
lean_inc(x_1365);
lean_dec(x_1364);
x_10 = x_1350;
x_11 = x_1365;
goto block_36;
}
}
else
{
lean_object* x_1366; 
lean_dec(x_2);
lean_dec(x_1);
x_1366 = lean_ctor_get(x_1349, 0);
lean_inc(x_1366);
lean_dec(x_1349);
if (lean_obj_tag(x_1366) == 0)
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; uint8_t x_1372; 
x_1367 = lean_ctor_get(x_1366, 0);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1366, 1);
lean_inc(x_1368);
lean_dec(x_1366);
x_1369 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1369, 0, x_1368);
x_1370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1370, 0, x_1369);
x_1371 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1367, x_1370, x_3, x_4, x_5, x_6, x_7, x_8, x_1343);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1367);
x_1372 = !lean_is_exclusive(x_1371);
if (x_1372 == 0)
{
return x_1371;
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1373 = lean_ctor_get(x_1371, 0);
x_1374 = lean_ctor_get(x_1371, 1);
lean_inc(x_1374);
lean_inc(x_1373);
lean_dec(x_1371);
x_1375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1375, 0, x_1373);
lean_ctor_set(x_1375, 1, x_1374);
return x_1375;
}
}
else
{
lean_object* x_1376; uint8_t x_1377; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1376 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1343);
x_1377 = !lean_is_exclusive(x_1376);
if (x_1377 == 0)
{
return x_1376;
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
x_1378 = lean_ctor_get(x_1376, 0);
x_1379 = lean_ctor_get(x_1376, 1);
lean_inc(x_1379);
lean_inc(x_1378);
lean_dec(x_1376);
x_1380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1380, 0, x_1378);
lean_ctor_set(x_1380, 1, x_1379);
return x_1380;
}
}
}
}
else
{
lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; 
x_1381 = l_Lean_Syntax_getArg(x_1332, x_135);
lean_dec(x_1332);
x_1382 = l_Lean_identKind___closed__2;
lean_inc(x_1381);
x_1383 = l_Lean_Syntax_isOfKind(x_1381, x_1382);
if (x_1383 == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
lean_dec(x_1381);
lean_dec(x_1283);
lean_dec(x_234);
x_1384 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_1384, 1);
lean_inc(x_1386);
lean_dec(x_1384);
x_1387 = lean_st_ref_get(x_8, x_1386);
x_1388 = lean_ctor_get(x_1387, 0);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1387, 1);
lean_inc(x_1389);
lean_dec(x_1387);
x_1390 = lean_ctor_get(x_1388, 0);
lean_inc(x_1390);
lean_dec(x_1388);
x_1391 = lean_st_ref_get(x_4, x_1389);
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1391, 1);
lean_inc(x_1393);
lean_dec(x_1391);
x_1394 = lean_ctor_get(x_1392, 3);
lean_inc(x_1394);
lean_dec(x_1392);
x_1395 = lean_ctor_get(x_7, 1);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_7, 2);
lean_inc(x_1396);
x_1397 = lean_environment_main_module(x_1390);
x_1398 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1385);
lean_ctor_set(x_1398, 2, x_1395);
lean_ctor_set(x_1398, 3, x_1396);
lean_inc(x_1);
x_1399 = l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f(x_1, x_1398, x_1394);
if (lean_obj_tag(x_1399) == 0)
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; uint8_t x_1405; 
x_1400 = lean_ctor_get(x_1399, 0);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1399, 1);
lean_inc(x_1401);
lean_dec(x_1399);
x_1402 = lean_st_ref_take(x_4, x_1393);
x_1403 = lean_ctor_get(x_1402, 0);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1402, 1);
lean_inc(x_1404);
lean_dec(x_1402);
x_1405 = !lean_is_exclusive(x_1403);
if (x_1405 == 0)
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
x_1406 = lean_ctor_get(x_1403, 3);
lean_dec(x_1406);
lean_ctor_set(x_1403, 3, x_1401);
x_1407 = lean_st_ref_set(x_4, x_1403, x_1404);
x_1408 = lean_ctor_get(x_1407, 1);
lean_inc(x_1408);
lean_dec(x_1407);
x_10 = x_1400;
x_11 = x_1408;
goto block_36;
}
else
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1409 = lean_ctor_get(x_1403, 0);
x_1410 = lean_ctor_get(x_1403, 1);
x_1411 = lean_ctor_get(x_1403, 2);
x_1412 = lean_ctor_get(x_1403, 4);
lean_inc(x_1412);
lean_inc(x_1411);
lean_inc(x_1410);
lean_inc(x_1409);
lean_dec(x_1403);
x_1413 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1413, 0, x_1409);
lean_ctor_set(x_1413, 1, x_1410);
lean_ctor_set(x_1413, 2, x_1411);
lean_ctor_set(x_1413, 3, x_1401);
lean_ctor_set(x_1413, 4, x_1412);
x_1414 = lean_st_ref_set(x_4, x_1413, x_1404);
x_1415 = lean_ctor_get(x_1414, 1);
lean_inc(x_1415);
lean_dec(x_1414);
x_10 = x_1400;
x_11 = x_1415;
goto block_36;
}
}
else
{
lean_object* x_1416; 
lean_dec(x_2);
lean_dec(x_1);
x_1416 = lean_ctor_get(x_1399, 0);
lean_inc(x_1416);
lean_dec(x_1399);
if (lean_obj_tag(x_1416) == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; uint8_t x_1422; 
x_1417 = lean_ctor_get(x_1416, 0);
lean_inc(x_1417);
x_1418 = lean_ctor_get(x_1416, 1);
lean_inc(x_1418);
lean_dec(x_1416);
x_1419 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1419, 0, x_1418);
x_1420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1420, 0, x_1419);
x_1421 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1417, x_1420, x_3, x_4, x_5, x_6, x_7, x_8, x_1393);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1417);
x_1422 = !lean_is_exclusive(x_1421);
if (x_1422 == 0)
{
return x_1421;
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
x_1423 = lean_ctor_get(x_1421, 0);
x_1424 = lean_ctor_get(x_1421, 1);
lean_inc(x_1424);
lean_inc(x_1423);
lean_dec(x_1421);
x_1425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1425, 0, x_1423);
lean_ctor_set(x_1425, 1, x_1424);
return x_1425;
}
}
else
{
lean_object* x_1426; uint8_t x_1427; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1426 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_26__elabCDot___spec__1___rarg(x_1393);
x_1427 = !lean_is_exclusive(x_1426);
if (x_1427 == 0)
{
return x_1426;
}
else
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1428 = lean_ctor_get(x_1426, 0);
x_1429 = lean_ctor_get(x_1426, 1);
lean_inc(x_1429);
lean_inc(x_1428);
lean_dec(x_1426);
x_1430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1430, 0, x_1428);
lean_ctor_set(x_1430, 1, x_1429);
return x_1430;
}
}
}
}
else
{
lean_object* x_1431; lean_object* x_1432; 
x_1431 = l_Lean_Syntax_getArg(x_1283, x_235);
lean_dec(x_1283);
x_1432 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_234, x_1381, x_1431, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1432;
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1() {
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
x_3 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_48__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10;
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
lean_object* _init_l_Lean_Elab_Term_elabNoMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nomatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabNoMatch___closed__2() {
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
lean_inc(x_3);
x_20 = l___private_Lean_Elab_Match_39__waitExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_19);
x_25 = l_Array_empty___closed__1;
x_26 = l_Lean_mkOptionalNode___closed__1;
x_27 = l___private_Lean_Elab_Match_38__elabMatchAux(x_24, x_25, x_26, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1() {
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
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__1 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__1);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__2 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__2);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__3);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__4 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__4);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__5 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__5);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__6 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__6);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__7 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__7);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__8 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__8);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__9 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__9);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__10);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__11 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__11);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__12 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__12);
l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13 = _init_l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___closed__13);
l_Lean_Elab_Term_mkInaccessible___closed__1 = _init_l_Lean_Elab_Term_mkInaccessible___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkInaccessible___closed__1);
l_Lean_Elab_Term_mkInaccessible___closed__2 = _init_l_Lean_Elab_Term_mkInaccessible___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkInaccessible___closed__2);
l_Lean_Elab_Term_PatternVar_hasToString___closed__1 = _init_l_Lean_Elab_Term_PatternVar_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_PatternVar_hasToString___closed__1);
l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1 = _init_l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1);
l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2 = _init_l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2);
res = l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind(lean_io_mk_world());
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
l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1 = _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1);
l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2 = _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2);
l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3 = _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3);
l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1 = _init_l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1);
l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1 = _init_l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1);
l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2 = _init_l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2);
l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3 = _init_l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__1);
l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_resolveId_x3f___closed__2);
l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__2);
l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__3 = _init_l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_15__throwInvalidPattern___rarg___closed__3);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited___closed__1);
l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited = _init_l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_CtorApp_Context_inhabited);
l___private_Lean_Elab_Match_17__finalize___closed__1 = _init_l___private_Lean_Elab_Match_17__finalize___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_17__finalize___closed__1);
l___private_Lean_Elab_Match_17__finalize___closed__2 = _init_l___private_Lean_Elab_Match_17__finalize___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_17__finalize___closed__2);
l___private_Lean_Elab_Match_17__finalize___closed__3 = _init_l___private_Lean_Elab_Match_17__finalize___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_17__finalize___closed__3);
l___private_Lean_Elab_Match_20__pushNewArg___closed__1 = _init_l___private_Lean_Elab_Match_20__pushNewArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_20__pushNewArg___closed__1);
l___private_Lean_Elab_Match_21__processExplicitArg___closed__1 = _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_21__processExplicitArg___closed__1);
l___private_Lean_Elab_Match_21__processExplicitArg___closed__2 = _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_21__processExplicitArg___closed__2);
l___private_Lean_Elab_Match_21__processExplicitArg___closed__3 = _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_21__processExplicitArg___closed__3);
l___private_Lean_Elab_Match_21__processExplicitArg___closed__4 = _init_l___private_Lean_Elab_Match_21__processExplicitArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_21__processExplicitArg___closed__4);
l___private_Lean_Elab_Match_24__processVar___closed__1 = _init_l___private_Lean_Elab_Match_24__processVar___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__1);
l___private_Lean_Elab_Match_24__processVar___closed__2 = _init_l___private_Lean_Elab_Match_24__processVar___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__2);
l___private_Lean_Elab_Match_24__processVar___closed__3 = _init_l___private_Lean_Elab_Match_24__processVar___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__3);
l___private_Lean_Elab_Match_24__processVar___closed__4 = _init_l___private_Lean_Elab_Match_24__processVar___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__4);
l___private_Lean_Elab_Match_24__processVar___closed__5 = _init_l___private_Lean_Elab_Match_24__processVar___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__5);
l___private_Lean_Elab_Match_24__processVar___closed__6 = _init_l___private_Lean_Elab_Match_24__processVar___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__6);
l___private_Lean_Elab_Match_24__processVar___closed__7 = _init_l___private_Lean_Elab_Match_24__processVar___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__7);
l___private_Lean_Elab_Match_24__processVar___closed__8 = _init_l___private_Lean_Elab_Match_24__processVar___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__8);
l___private_Lean_Elab_Match_24__processVar___closed__9 = _init_l___private_Lean_Elab_Match_24__processVar___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_24__processVar___closed__9);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__1);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__2 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__2);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__3);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__4);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__5 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__5);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__6);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__7);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__8);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__9);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__10 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__10);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__11 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__11);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__12);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__13);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__14 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__14);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__15);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__16);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__17);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__18 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__18);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__19 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__19);
l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20 = _init_l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Match_26__nameToPattern___main___closed__20);
l___private_Lean_Elab_Match_28__collect___main___closed__1 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__1);
l___private_Lean_Elab_Match_28__collect___main___closed__2 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__2);
l___private_Lean_Elab_Match_28__collect___main___closed__3 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__3);
l___private_Lean_Elab_Match_28__collect___main___closed__4 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__4);
l___private_Lean_Elab_Match_28__collect___main___closed__5 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__5);
l___private_Lean_Elab_Match_28__collect___main___closed__6 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__6);
l___private_Lean_Elab_Match_28__collect___main___closed__7 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__7);
l___private_Lean_Elab_Match_28__collect___main___closed__8 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__8);
l___private_Lean_Elab_Match_28__collect___main___closed__9 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__9);
l___private_Lean_Elab_Match_28__collect___main___closed__10 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__10);
l___private_Lean_Elab_Match_28__collect___main___closed__11 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__11);
l___private_Lean_Elab_Match_28__collect___main___closed__12 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__12);
l___private_Lean_Elab_Match_28__collect___main___closed__13 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__13);
l___private_Lean_Elab_Match_28__collect___main___closed__14 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__14);
l___private_Lean_Elab_Match_28__collect___main___closed__15 = _init_l___private_Lean_Elab_Match_28__collect___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Match_28__collect___main___closed__15);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3);
l___private_Lean_Elab_Match_29__collectPatternVars___closed__1 = _init_l___private_Lean_Elab_Match_29__collectPatternVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_29__collectPatternVars___closed__1);
l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__1 = _init_l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__1);
l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__2 = _init_l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__2);
l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__3 = _init_l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabPatternsAux___main___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9);
l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__2);
l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__3 = _init_l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_35__throwInvalidPattern___rarg___closed__3);
l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1);
l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2);
l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3 = _init_l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2);
l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3);
l_Lean_Elab_Term_elabMatchAltView___closed__1 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__1);
l_Lean_Elab_Term_elabMatchAltView___closed__2 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__2);
l_Lean_Elab_Term_elabMatchAltView___closed__3 = _init_l_Lean_Elab_Term_elabMatchAltView___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabMatchAltView___closed__3);
l_Lean_Elab_Term_mkMotiveType___closed__1 = _init_l_Lean_Elab_Term_mkMotiveType___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkMotiveType___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__1 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__1);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__2 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__2);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__3 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__3);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__4 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__4);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__5 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__5);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__6 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__6);
l_Lean_Elab_Term_reportMatcherResultErrors___closed__7 = _init_l_Lean_Elab_Term_reportMatcherResultErrors___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_reportMatcherResultErrors___closed__7);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__1 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__1);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__2 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__2);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__3 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__3);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__4 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__4);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__5 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__5);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__6 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__6);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__7 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__7);
l___private_Lean_Elab_Match_38__elabMatchAux___closed__8 = _init_l___private_Lean_Elab_Match_38__elabMatchAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_38__elabMatchAux___closed__8);
l___private_Lean_Elab_Match_41__mkMatchType___main___closed__1 = _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_41__mkMatchType___main___closed__1);
l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2 = _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_41__mkMatchType___main___closed__2);
l___private_Lean_Elab_Match_41__mkMatchType___main___closed__3 = _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_41__mkMatchType___main___closed__3);
l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4 = _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_41__mkMatchType___main___closed__4);
l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5 = _init_l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_41__mkMatchType___main___closed__5);
l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1 = _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__1);
l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__2 = _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__2);
l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__3 = _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__3);
l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__4 = _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__4);
l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__5 = _init_l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_43__mkNewDiscrs___main___closed__5);
l___private_Lean_Elab_Match_44__mkNewPatterns___main___closed__1 = _init_l___private_Lean_Elab_Match_44__mkNewPatterns___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_44__mkNewPatterns___main___closed__1);
l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___closed__1 = _init_l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_47__expandMatchDiscr_x3f___closed__1);
l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Match_48__regTraceClasses(lean_io_mk_world());
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
