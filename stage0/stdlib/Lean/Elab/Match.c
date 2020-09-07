// Lean compiler output
// Module: Lean.Elab.Match
// Imports: Init Lean.Meta.EqnCompiler.MatchPatternAttr Lean.Meta.EqnCompiler.Match Lean.Elab.SyntheticMVars
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
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__4;
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__1;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId___boxed(lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__4;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__4;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_12__addAssignmentInfo___closed__4;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__9;
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabImplicitLambda___main___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__8;
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__2;
lean_object* l___private_Lean_Elab_Match_16__processIdAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__13;
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__9;
lean_object* l_Lean_Elab_Term_reportElimResultErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__18;
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__1;
lean_object* l_Lean_Elab_Term_mkMotiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_18__processId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_23__withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_36__mkOptType(lean_object*);
lean_object* l_Lean_Elab_Term_mkElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithIdImpl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_40__mkNewAlts(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_15__processVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__3;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__9;
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2;
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__6;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1;
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_17__processCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern(lean_object*);
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__2;
lean_object* l___private_Lean_Elab_Match_33__waitExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__5;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8;
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__hasCDot___main___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__4;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__12;
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__45;
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__4;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_42__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
lean_object* l_Lean_Elab_Term_reportElimResultErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_29__mkLocalDeclFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__1;
lean_object* l___private_Lean_Elab_Match_26__markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(uint8_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__19;
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern(lean_object*);
extern lean_object* l_Lean_EqnCompiler_matchPatternAttr;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__11;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__1;
lean_object* l___private_Lean_Elab_Match_26__markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_33__waitExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__5;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__2;
lean_object* l_Lean_Meta_instantiateLocalDeclMVars___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabNoMatch___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__17;
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__2;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__8;
lean_object* l___private_Lean_Elab_Match_30__getFieldsBinderInfo(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_39__mkNewAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind;
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2;
lean_object* l_Lean_Elab_expandMacros___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__7;
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
extern lean_object* l_Lean_Elab_Term_elabForall___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__1;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__7;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
extern lean_object* l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__16;
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__3;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_34__elabMatchCore___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
lean_object* l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_29__mkLocalDeclFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___lambda__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__2;
lean_object* l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__1;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__7;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__7;
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__3;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_BinderInfo_inhabited;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_MessageData_coeOfListExpr___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__6;
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5;
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__7;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3;
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_30__getFieldsBinderInfo___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__3;
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__5;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_40__mkNewAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_object* l_Lean_Elab_Term_mkMotiveType___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_18__processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__3;
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_23__withPatternVars(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__28;
lean_object* l___private_Lean_Elab_Match_20__collect___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__8;
extern lean_object* l___private_Lean_Elab_Binders_6__matchBinder___closed__2;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_39__mkNewAlt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__6;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__5;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__4;
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__3;
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__1;
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
lean_object* l_List_toString___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__3;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__6;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_13__isExplicit___closed__2;
lean_object* l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(uint8_t, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__5;
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__3;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__18;
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__5;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_17__processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__8;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__15;
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__2___closed__9;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabParen___closed__7;
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__10;
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__10;
lean_object* l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___closed__14;
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_object*);
lean_object* l_Lean_mkThunk(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6;
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_5, x_4, x_2, x_6);
lean_dec(x_4);
x_8 = l_Lean_Syntax_getArg(x_1, x_5);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
return x_9;
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
x_19 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
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
x_20 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
x_21 = lean_array_push(x_19, x_20);
x_22 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
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
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_6__matchBinder___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
x_2 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_8, x_3, x_4);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Elab_Term_elabForall___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Syntax_copyInfo(x_15, x_1);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
x_20 = lean_array_push(x_19, x_17);
x_21 = l_Lean_Elab_Term_elabForall___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Syntax_copyInfo(x_22, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkHole(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Syntax_isNone(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_3, x_4, x_5);
return x_12;
}
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
x_11 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_4, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 5);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 2);
lean_inc(x_23);
x_24 = lean_environment_main_module(x_17);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
x_26 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_10, x_1, x_2, x_25, x_21);
lean_dec(x_25);
lean_dec(x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_4, x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 5);
lean_dec(x_33);
lean_ctor_set(x_30, 5, x_28);
x_34 = lean_st_ref_set(x_4, x_30, x_31);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Term_elabType(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
x_39 = lean_ctor_get(x_30, 2);
x_40 = lean_ctor_get(x_30, 3);
x_41 = lean_ctor_get(x_30, 4);
x_42 = lean_ctor_get(x_30, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_43, 5, x_28);
lean_ctor_set(x_43, 6, x_42);
x_44 = lean_st_ref_set(x_4, x_43, x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Elab_Term_elabType(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
return x_46;
}
}
}
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_5__elabMatchOptType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(uint8_t x_1, lean_object* x_2) {
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
x_10 = l_Lean_Options_empty;
x_11 = l_Lean_Format_pretty(x_9, x_10);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(x_1, x_5);
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
x_23 = l_Lean_Options_empty;
x_24 = l_Lean_Format_pretty(x_22, x_23);
x_25 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(x_20, x_18);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
}
}
lean_object* l_List_toString___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__1(lean_object* x_1) {
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
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid result type provided to match-expression");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid type provided to match-expression, function type with arity #");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discr #");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_15 = l_Lean_Elab_Term_isDefEq(x_4, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_5);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_4);
x_20 = l_Lean_indentExpr(x_19);
x_21 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_MessageData_ofList___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l_Lean_indentExpr(x_27);
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_15, 0);
lean_dec(x_36);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
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
lean_dec(x_4);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_array_fget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_44 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 7)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 2);
lean_inc(x_61);
lean_dec(x_45);
lean_inc(x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_63 = l_Lean_Elab_Term_elabTermEnsuringType(x_43, x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_10, 0);
lean_inc(x_66);
x_67 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_68 = l_Lean_checkTraceOption(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_3, x_69);
lean_dec(x_3);
x_71 = lean_expr_instantiate1(x_61, x_64);
lean_dec(x_61);
x_72 = lean_array_push(x_5, x_64);
x_3 = x_70;
x_4 = x_71;
x_5 = x_72;
x_12 = x_65;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_inc(x_3);
x_74 = l_Nat_repr(x_3);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l___private_Lean_Meta_ExprDefEq_12__addAssignmentInfo___closed__4;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_64);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_64);
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_60);
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_67, x_86, x_6, x_7, x_8, x_9, x_10, x_11, x_65);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_3, x_89);
lean_dec(x_3);
x_91 = lean_expr_instantiate1(x_61, x_64);
lean_dec(x_61);
x_92 = lean_array_push(x_5, x_64);
x_3 = x_90;
x_4 = x_91;
x_5 = x_92;
x_12 = x_88;
goto _start;
}
}
else
{
uint8_t x_94; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_63);
if (x_94 == 0)
{
return x_63;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_63, 0);
x_96 = lean_ctor_get(x_63, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_63);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_box(0);
x_47 = x_98;
goto block_59;
}
block_59:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_47);
x_48 = l_Array_toList___rarg(x_1);
x_49 = l_List_toString___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__1(x_48);
x_50 = l_Array_HasRepr___rarg___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_58;
}
}
else
{
uint8_t x_99; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
return x_44;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_44, 0);
x_101 = lean_ctor_get(x_44, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_44);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_6__elabDiscrsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main(x_1, x_3, x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Match_7__elabDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
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
x_43 = lean_ctor_get(x_41, 5);
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
x_56 = lean_ctor_get(x_53, 5);
lean_dec(x_56);
lean_ctor_set(x_53, 5, x_51);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
x_61 = lean_ctor_get(x_53, 2);
x_62 = lean_ctor_get(x_53, 3);
x_63 = lean_ctor_get(x_53, 4);
x_64 = lean_ctor_get(x_53, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
x_65 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_51);
lean_ctor_set(x_65, 6, x_64);
x_66 = lean_st_ref_set(x_5, x_65, x_54);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
lean_ctor_set(x_26, 1, x_50);
x_18 = x_26;
x_19 = x_67;
goto block_25;
}
}
else
{
lean_object* x_68; 
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_49, 0);
lean_inc(x_68);
lean_dec(x_49);
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
x_73 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_69, x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
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
lean_dec(x_4);
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(x_42);
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
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_83 = lean_ctor_get(x_26, 0);
x_84 = lean_ctor_get(x_26, 1);
x_85 = lean_ctor_get(x_26, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_26);
x_86 = x_84;
lean_inc(x_1);
x_87 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_87, 0, x_1);
lean_closure_set(x_87, 1, x_16);
lean_closure_set(x_87, 2, x_86);
x_88 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_9, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_5, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 5);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_8, 1);
x_100 = lean_ctor_get(x_8, 2);
x_101 = lean_environment_main_module(x_94);
lean_inc(x_100);
lean_inc(x_99);
x_102 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_89);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_100);
x_103 = x_87;
x_104 = lean_apply_2(x_103, x_102, x_98);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_take(x_5, x_97);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 6);
lean_inc(x_115);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 lean_ctor_release(x_108, 5);
 lean_ctor_release(x_108, 6);
 x_116 = x_108;
} else {
 lean_dec_ref(x_108);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 7, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_111);
lean_ctor_set(x_117, 2, x_112);
lean_ctor_set(x_117, 3, x_113);
lean_ctor_set(x_117, 4, x_114);
lean_ctor_set(x_117, 5, x_106);
lean_ctor_set(x_117, 6, x_115);
x_118 = lean_st_ref_set(x_5, x_117, x_109);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_83);
lean_ctor_set(x_120, 1, x_105);
lean_ctor_set(x_120, 2, x_85);
x_18 = x_120;
x_19 = x_119;
goto block_25;
}
else
{
lean_object* x_121; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_104, 0);
lean_inc(x_121);
lean_dec(x_104);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_122, x_125, x_4, x_5, x_6, x_7, x_8, x_9, x_97);
lean_dec(x_122);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_4);
x_131 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2___rarg(x_97);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
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
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Lean_Elab_Term_mkMatchAltView(x_9);
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
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_filterAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__1(x_6, x_7, x_7);
x_9 = x_8;
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__2(x_7, x_9);
x_11 = x_10;
return x_11;
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
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_19 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg___lambda__1), 10, 3);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(x_1, x_1, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_14 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg(x_10, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_10 = l_List_map___main___at_Lean_MessageData_coeOfListExpr___spec__1(x_1);
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
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, variable '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__processVar___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__processVar___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurred more than once");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__processVar___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__processVar___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern variable, must be atomic");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__processVar___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_15__processVar___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_15__processVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
if (x_2 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Name_eraseMacroScopes(x_1);
x_42 = l_Lean_Name_isAtomic(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_43 = l___private_Lean_Elab_Match_15__processVar___closed__9;
x_44 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_st_ref_get(x_3, x_10);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_11 = x_50;
x_12 = x_51;
goto block_40;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_1);
x_52 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
block_40:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_NameSet_contains(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
x_15 = lean_st_ref_take(x_3, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_box(0);
lean_inc(x_1);
x_20 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_18, x_1, x_19);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_1);
x_31 = l___private_Lean_Elab_Match_15__processVar___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Elab_Match_15__processVar___closed__6;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_15__processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_Match_15__processVar(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_35; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
lean_inc(x_27);
lean_inc(x_3);
x_35 = lean_environment_find(x_3, x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_3);
x_36 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 6)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_3);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = lean_box(0);
x_28 = x_40;
goto block_34;
}
}
block_34:
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_28);
x_29 = l_Lean_EqnCompiler_matchPatternAttr;
x_30 = l_Lean_TagAttribute_hasTag(x_29, x_3, x_27);
lean_dec(x_27);
lean_dec(x_3);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_13 = x_31;
goto block_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_box(0);
x_13 = x_41;
goto block_26;
}
block_26:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
x_14 = l_Lean_Syntax_getId(x_1);
x_15 = l___private_Lean_Elab_Match_15__processVar(x_14, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(lean_object* x_1) {
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
x_6 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_5);
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
x_10 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_9);
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
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected, '@' is not allowed in patterns");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_16__processIdAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_16__processIdAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__1(x_1, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_16__processIdAux___closed__4;
x_2 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_13);
x_15 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_15);
x_16 = lean_st_ref_get(x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_31 = l_Lean_Elab_Term_resolveName(x_28, x_29, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__1(x_32, x_30);
x_35 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_19);
x_36 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_37 = l___private_Lean_Elab_Match_15__processVar(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_35, 0);
lean_inc(x_49);
lean_dec(x_35);
x_50 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_2, x_19, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_1);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_19);
lean_dec(x_1);
x_51 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec(x_31);
x_53 = l___private_Lean_Elab_Match_16__processIdAux___closed__5;
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
x_54 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_55 = l___private_Lean_Elab_Match_15__processVar(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_55, 0);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_55);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_53, 0);
lean_inc(x_67);
x_68 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_2, x_19, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_1);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_1);
x_69 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_69;
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_19);
x_70 = lean_box(0);
x_20 = x_70;
goto block_27;
}
block_27:
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_20);
x_21 = l___private_Lean_Elab_Term_13__isExplicit___closed__2;
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_24 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Elab_Match_16__processIdAux___closed__3;
x_26 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_26;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_8, 0);
x_72 = lean_ctor_get(x_8, 1);
x_73 = lean_ctor_get(x_8, 2);
x_74 = lean_ctor_get(x_8, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_8);
x_75 = l_Lean_replaceRef(x_1, x_74);
x_76 = l_Lean_replaceRef(x_75, x_74);
lean_dec(x_75);
x_77 = l_Lean_replaceRef(x_76, x_74);
lean_dec(x_74);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_77);
x_79 = lean_st_ref_get(x_9, x_10);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 3);
lean_inc(x_92);
x_93 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_94 = l_Lean_Elab_Term_resolveName(x_91, x_92, x_93, x_4, x_5, x_6, x_7, x_78, x_9, x_81);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__1(x_95, x_93);
x_98 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_82);
x_99 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_100 = l___private_Lean_Elab_Match_15__processVar(x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_96);
lean_dec(x_9);
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_107 = x_100;
} else {
 lean_dec_ref(x_100);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_98, 0);
lean_inc(x_110);
lean_dec(x_98);
x_111 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_2, x_82, x_110, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_96);
lean_dec(x_1);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_82);
lean_dec(x_1);
x_112 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_98, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_96);
lean_dec(x_9);
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
lean_dec(x_94);
x_114 = l___private_Lean_Elab_Match_16__processIdAux___closed__5;
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_82);
x_115 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_116 = l___private_Lean_Elab_Match_15__processVar(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_113);
lean_dec(x_9);
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
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
x_119 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
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
}
else
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_114, 1);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
x_127 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_2, x_82, x_126, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_113);
lean_dec(x_1);
return x_127;
}
else
{
lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_82);
lean_dec(x_1);
x_128 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_114, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_113);
lean_dec(x_9);
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_128;
}
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_82);
x_129 = lean_box(0);
x_83 = x_129;
goto block_90;
}
block_90:
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_83);
x_84 = l___private_Lean_Elab_Term_13__isExplicit___closed__2;
x_85 = l_Lean_Syntax_isOfKind(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_87 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_86, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_81);
lean_dec(x_9);
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l___private_Lean_Elab_Match_16__processIdAux___closed__3;
x_89 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_88, x_3, x_4, x_5, x_6, x_7, x_78, x_9, x_81);
lean_dec(x_9);
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_89;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_Match_16__processIdAux(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_17__processCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l___private_Lean_Elab_Match_16__processIdAux(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_17__processCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_17__processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_18__processId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l___private_Lean_Elab_Match_16__processIdAux(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
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
lean_object* l___private_Lean_Elab_Match_18__processId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_18__processId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPattern");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("named parameters are not allowed in patterns");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_array_fget(x_2, x_3);
x_17 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1;
lean_inc(x_1);
x_18 = lean_name_mk_string(x_1, x_17);
lean_inc(x_16);
x_19 = l_Lean_Syntax_isOfKind(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_23 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__4;
x_24 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_16, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
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
lean_dec(x_4);
lean_dec(x_2);
x_14 = x_3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_fget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fset(x_3, x_2, x_17);
x_19 = x_16;
x_20 = lean_nat_dec_lt(x_2, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Elab_Match_20__collect___main(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
x_26 = x_22;
x_27 = lean_array_fset(x_18, x_2, x_26);
lean_dec(x_2);
x_2 = x_25;
x_3 = x_27;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
x_35 = x_19;
x_36 = lean_array_fset(x_18, x_2, x_35);
lean_dec(x_2);
x_2 = x_34;
x_3 = x_36;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l___private_Lean_Elab_Match_20__collect___main(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymousCtor");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Match_20__collect___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitUniv");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Match_20__collect___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, notation is ambiguous");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_20__collect___main___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_20__collect___main___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_20__collect___main), 9, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid struct instance pattern, 'with' is not allowed in patterns");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_20__collect___main___lambda__1), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_20__collect___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; 
x_1267 = lean_ctor_get(x_19, 0);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_19, 1);
lean_inc(x_1268);
lean_dec(x_19);
x_1269 = 0;
x_20 = x_1269;
x_21 = x_1267;
x_22 = x_1268;
goto block_1266;
}
else
{
lean_object* x_1270; lean_object* x_1271; uint8_t x_1272; 
x_1270 = lean_ctor_get(x_19, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_19, 1);
lean_inc(x_1271);
lean_dec(x_19);
x_1272 = 1;
x_20 = x_1272;
x_21 = x_1270;
x_22 = x_1271;
goto block_1266;
}
block_1266:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_21, 5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_ctor_set(x_21, 5, x_26);
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
x_33 = l___private_Lean_Elab_Match_20__collect___main___closed__2;
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
x_39 = l___private_Lean_Elab_Term_5__hasCDot___main___closed__1;
x_40 = lean_name_eq(x_10, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_11);
x_41 = l___private_Lean_Elab_Match_20__collect___main___closed__4;
x_42 = lean_name_eq(x_10, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l___private_Lean_Elab_Match_20__collect___main___closed__5;
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
lean_dec(x_1);
x_53 = l_Lean_choiceKind;
x_54 = lean_name_eq(x_10, x_53);
lean_dec(x_10);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l___private_Lean_Elab_Match_20__collect___main___closed__8;
x_57 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_57;
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
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
lean_free_object(x_27);
lean_dec(x_10);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Syntax_getArg(x_1, x_58);
x_60 = l_Lean_Syntax_getId(x_59);
x_61 = 0;
lean_inc(x_3);
x_62 = l___private_Lean_Elab_Match_15__processVar(x_60, x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_unsigned_to_nat(2u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
x_66 = !lean_is_exclusive(x_1);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_1, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_1, 0);
lean_dec(x_68);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = l___private_Lean_Elab_Match_20__collect___main(x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_74);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_79 = l_Lean_addMacroScope(x_77, x_78, x_73);
x_80 = l_Lean_SourceInfo_inhabited___closed__1;
x_81 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_82 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_82);
x_84 = l_Array_empty___closed__1;
x_85 = lean_array_push(x_84, x_83);
x_86 = lean_array_push(x_84, x_59);
x_87 = lean_array_push(x_86, x_70);
x_88 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_87);
lean_ctor_set(x_1, 0, x_88);
x_89 = lean_array_push(x_85, x_1);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_75, 0, x_90);
return x_75;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_91 = lean_ctor_get(x_75, 0);
x_92 = lean_ctor_get(x_75, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_75);
x_93 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_94 = l_Lean_addMacroScope(x_91, x_93, x_73);
x_95 = l_Lean_SourceInfo_inhabited___closed__1;
x_96 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_97 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_98 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_97);
x_99 = l_Array_empty___closed__1;
x_100 = lean_array_push(x_99, x_98);
x_101 = lean_array_push(x_99, x_59);
x_102 = lean_array_push(x_101, x_70);
x_103 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_103);
x_104 = lean_array_push(x_100, x_1);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_12);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_92);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_free_object(x_1);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_107 = !lean_is_exclusive(x_69);
if (x_107 == 0)
{
return x_69;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_69, 0);
x_109 = lean_ctor_get(x_69, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_69);
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
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_111 = l___private_Lean_Elab_Match_20__collect___main(x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_113);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_116);
lean_dec(x_8);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_122 = l_Lean_addMacroScope(x_118, x_121, x_115);
x_123 = l_Lean_SourceInfo_inhabited___closed__1;
x_124 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_125 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_126 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_122);
lean_ctor_set(x_126, 3, x_125);
x_127 = l_Array_empty___closed__1;
x_128 = lean_array_push(x_127, x_126);
x_129 = lean_array_push(x_127, x_59);
x_130 = lean_array_push(x_129, x_112);
x_131 = l_Lean_nullKind___closed__2;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_push(x_128, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_12);
lean_ctor_set(x_134, 1, x_133);
if (lean_is_scalar(x_120)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_120;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_119);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_136 = lean_ctor_get(x_111, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_111, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_138 = x_111;
} else {
 lean_dec_ref(x_111);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_62);
if (x_140 == 0)
{
return x_62;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_62, 0);
x_142 = lean_ctor_get(x_62, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_62);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
lean_free_object(x_27);
lean_dec(x_10);
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_Lean_Syntax_getArg(x_1, x_144);
x_146 = 1;
x_147 = l___private_Lean_Elab_Match_16__processIdAux(x_145, x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_2);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_dec(x_149);
lean_ctor_set(x_147, 0, x_1);
return x_147;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_1);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
else
{
uint8_t x_152; 
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_147);
if (x_152 == 0)
{
return x_147;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_147, 0);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_147);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = l_Lean_Syntax_inhabited;
x_157 = lean_array_get(x_156, x_11, x_25);
x_158 = l_Lean_Syntax_isNone(x_157);
if (x_158 == 0)
{
uint8_t x_159; 
lean_free_object(x_27);
x_159 = !lean_is_exclusive(x_1);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_1, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_1, 0);
lean_dec(x_161);
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Lean_Syntax_getArg(x_157, x_162);
x_164 = l_Lean_Syntax_getArg(x_157, x_25);
x_165 = l_Lean_Syntax_isNone(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = l_Lean_Syntax_getArg(x_164, x_162);
x_167 = l_Lean_Elab_Term_elabParen___closed__7;
lean_inc(x_166);
x_168 = l_Lean_Syntax_isOfKind(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_169 = l___private_Lean_Elab_Match_20__collect___main(x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Syntax_setArg(x_157, x_162, x_170);
x_173 = l_Lean_Syntax_getArg(x_166, x_25);
x_174 = l_Lean_Syntax_getArgs(x_173);
lean_dec(x_173);
x_175 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_176 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_174, x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_174);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_179);
x_180 = l_Lean_Syntax_setArg(x_166, x_25, x_1);
x_181 = l_Lean_Syntax_setArg(x_164, x_162, x_180);
x_182 = l_Lean_Syntax_setArg(x_172, x_25, x_181);
x_183 = lean_array_set(x_11, x_25, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_10);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_176, 0, x_184);
return x_176;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_185 = lean_ctor_get(x_176, 0);
x_186 = lean_ctor_get(x_176, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_176);
x_187 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_185);
lean_ctor_set(x_1, 0, x_187);
x_188 = l_Lean_Syntax_setArg(x_166, x_25, x_1);
x_189 = l_Lean_Syntax_setArg(x_164, x_162, x_188);
x_190 = l_Lean_Syntax_setArg(x_172, x_25, x_189);
x_191 = lean_array_set(x_11, x_25, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_10);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_186);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_172);
lean_dec(x_166);
lean_dec(x_164);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_194 = !lean_is_exclusive(x_176);
if (x_194 == 0)
{
return x_176;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_176, 0);
x_196 = lean_ctor_get(x_176, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_176);
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
lean_dec(x_166);
lean_dec(x_164);
lean_free_object(x_1);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_169);
if (x_198 == 0)
{
return x_169;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_169, 0);
x_200 = lean_ctor_get(x_169, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_169);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_166);
lean_dec(x_164);
x_202 = l___private_Lean_Elab_Match_20__collect___main(x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = l_Lean_Syntax_setArg(x_157, x_162, x_204);
x_206 = lean_array_set(x_11, x_25, x_205);
lean_ctor_set(x_1, 1, x_206);
lean_ctor_set(x_202, 0, x_1);
return x_202;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_202, 0);
x_208 = lean_ctor_get(x_202, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_202);
x_209 = l_Lean_Syntax_setArg(x_157, x_162, x_207);
x_210 = lean_array_set(x_11, x_25, x_209);
lean_ctor_set(x_1, 1, x_210);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_1);
lean_ctor_set(x_211, 1, x_208);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_free_object(x_1);
lean_dec(x_157);
lean_dec(x_11);
lean_dec(x_10);
x_212 = !lean_is_exclusive(x_202);
if (x_212 == 0)
{
return x_202;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_202, 0);
x_214 = lean_ctor_get(x_202, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_202);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
else
{
lean_object* x_216; 
lean_dec(x_164);
x_216 = l___private_Lean_Elab_Match_20__collect___main(x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 0);
x_219 = l_Lean_Syntax_setArg(x_157, x_162, x_218);
x_220 = lean_array_set(x_11, x_25, x_219);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_216, 0, x_1);
return x_216;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_216, 0);
x_222 = lean_ctor_get(x_216, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_216);
x_223 = l_Lean_Syntax_setArg(x_157, x_162, x_221);
x_224 = lean_array_set(x_11, x_25, x_223);
lean_ctor_set(x_1, 1, x_224);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_1);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
}
else
{
uint8_t x_226; 
lean_free_object(x_1);
lean_dec(x_157);
lean_dec(x_11);
lean_dec(x_10);
x_226 = !lean_is_exclusive(x_216);
if (x_226 == 0)
{
return x_216;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_216, 0);
x_228 = lean_ctor_get(x_216, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_216);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_dec(x_1);
x_230 = lean_unsigned_to_nat(0u);
x_231 = l_Lean_Syntax_getArg(x_157, x_230);
x_232 = l_Lean_Syntax_getArg(x_157, x_25);
x_233 = l_Lean_Syntax_isNone(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = l_Lean_Syntax_getArg(x_232, x_230);
x_235 = l_Lean_Elab_Term_elabParen___closed__7;
lean_inc(x_234);
x_236 = l_Lean_Syntax_isOfKind(x_234, x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_237 = l___private_Lean_Elab_Match_20__collect___main(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Syntax_setArg(x_157, x_230, x_238);
x_241 = l_Lean_Syntax_getArg(x_234, x_25);
x_242 = l_Lean_Syntax_getArgs(x_241);
lean_dec(x_241);
x_243 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_244 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_242, x_243, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239);
lean_dec(x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = l_Lean_nullKind;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_245);
x_250 = l_Lean_Syntax_setArg(x_234, x_25, x_249);
x_251 = l_Lean_Syntax_setArg(x_232, x_230, x_250);
x_252 = l_Lean_Syntax_setArg(x_240, x_25, x_251);
x_253 = lean_array_set(x_11, x_25, x_252);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_10);
lean_ctor_set(x_254, 1, x_253);
if (lean_is_scalar(x_247)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_247;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_246);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_240);
lean_dec(x_234);
lean_dec(x_232);
lean_dec(x_11);
lean_dec(x_10);
x_256 = lean_ctor_get(x_244, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_244, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_258 = x_244;
} else {
 lean_dec_ref(x_244);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_234);
lean_dec(x_232);
lean_dec(x_157);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_260 = lean_ctor_get(x_237, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_237, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_262 = x_237;
} else {
 lean_dec_ref(x_237);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; 
lean_dec(x_234);
lean_dec(x_232);
x_264 = l___private_Lean_Elab_Match_20__collect___main(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
x_268 = l_Lean_Syntax_setArg(x_157, x_230, x_265);
x_269 = lean_array_set(x_11, x_25, x_268);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_10);
lean_ctor_set(x_270, 1, x_269);
if (lean_is_scalar(x_267)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_267;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_266);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_157);
lean_dec(x_11);
lean_dec(x_10);
x_272 = lean_ctor_get(x_264, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_264, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_274 = x_264;
} else {
 lean_dec_ref(x_264);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
else
{
lean_object* x_276; 
lean_dec(x_232);
x_276 = l___private_Lean_Elab_Match_20__collect___main(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = l_Lean_Syntax_setArg(x_157, x_230, x_277);
x_281 = lean_array_set(x_11, x_25, x_280);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_10);
lean_ctor_set(x_282, 1, x_281);
if (lean_is_scalar(x_279)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_279;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_278);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_157);
lean_dec(x_11);
lean_dec(x_10);
x_284 = lean_ctor_get(x_276, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_276, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_286 = x_276;
} else {
 lean_dec_ref(x_276);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
}
}
else
{
lean_dec(x_157);
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
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
lean_dec(x_3);
lean_free_object(x_27);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_288 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_29);
lean_dec(x_8);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
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
x_296 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_289);
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
lean_ctor_set(x_299, 0, x_289);
return x_299;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_289);
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
x_306 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_289);
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
lean_ctor_set(x_313, 0, x_289);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_free_object(x_27);
x_314 = !lean_is_exclusive(x_1);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 1);
lean_dec(x_315);
x_316 = lean_ctor_get(x_1, 0);
lean_dec(x_316);
x_317 = l_Lean_Syntax_inhabited;
x_318 = lean_array_get(x_317, x_11, x_25);
x_319 = l_Lean_Syntax_isNone(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_320 = l___private_Lean_Elab_Match_20__collect___main___closed__17;
x_321 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_318, x_320, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_318);
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
return x_321;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_321, 0);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_321);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_318);
x_326 = lean_unsigned_to_nat(2u);
x_327 = lean_array_get(x_317, x_11, x_326);
x_328 = l_Lean_Syntax_getArgs(x_327);
lean_dec(x_327);
x_329 = l___private_Lean_Elab_Match_20__collect___main___closed__18;
x_330 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_328, x_329, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_328);
if (lean_obj_tag(x_330) == 0)
{
uint8_t x_331; 
x_331 = !lean_is_exclusive(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_330, 0);
x_333 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_332);
lean_ctor_set(x_1, 0, x_333);
x_334 = lean_array_set(x_11, x_326, x_1);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_10);
lean_ctor_set(x_335, 1, x_334);
lean_ctor_set(x_330, 0, x_335);
return x_330;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_336 = lean_ctor_get(x_330, 0);
x_337 = lean_ctor_get(x_330, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_330);
x_338 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_336);
lean_ctor_set(x_1, 0, x_338);
x_339 = lean_array_set(x_11, x_326, x_1);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_10);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_337);
return x_341;
}
}
else
{
uint8_t x_342; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_342 = !lean_is_exclusive(x_330);
if (x_342 == 0)
{
return x_330;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_330, 0);
x_344 = lean_ctor_get(x_330, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_330);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
}
else
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; 
lean_dec(x_1);
x_346 = l_Lean_Syntax_inhabited;
x_347 = lean_array_get(x_346, x_11, x_25);
x_348 = l_Lean_Syntax_isNone(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_11);
lean_dec(x_10);
x_349 = l___private_Lean_Elab_Match_20__collect___main___closed__17;
x_350 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_347, x_349, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_347);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_353 = x_350;
} else {
 lean_dec_ref(x_350);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_347);
x_355 = lean_unsigned_to_nat(2u);
x_356 = lean_array_get(x_346, x_11, x_355);
x_357 = l_Lean_Syntax_getArgs(x_356);
lean_dec(x_356);
x_358 = l___private_Lean_Elab_Match_20__collect___main___closed__18;
x_359 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_357, x_358, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_357);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
x_363 = l_Lean_nullKind;
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_360);
x_365 = lean_array_set(x_11, x_355, x_364);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_10);
lean_ctor_set(x_366, 1, x_365);
if (lean_is_scalar(x_362)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_362;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_361);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_11);
lean_dec(x_10);
x_368 = lean_ctor_get(x_359, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_359, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_370 = x_359;
} else {
 lean_dec_ref(x_359);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
}
}
}
else
{
uint8_t x_372; 
lean_free_object(x_27);
x_372 = !lean_is_exclusive(x_1);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_373 = lean_ctor_get(x_1, 1);
lean_dec(x_373);
x_374 = lean_ctor_get(x_1, 0);
lean_dec(x_374);
x_375 = l_Lean_Syntax_inhabited;
x_376 = lean_array_get(x_375, x_11, x_25);
x_377 = l_Lean_Syntax_getArgs(x_376);
lean_dec(x_376);
x_378 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_379 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_377, x_378, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_377);
if (lean_obj_tag(x_379) == 0)
{
uint8_t x_380; 
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_381 = lean_ctor_get(x_379, 0);
x_382 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_381);
lean_ctor_set(x_1, 0, x_382);
x_383 = lean_array_set(x_11, x_25, x_1);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_10);
lean_ctor_set(x_384, 1, x_383);
lean_ctor_set(x_379, 0, x_384);
return x_379;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_379, 0);
x_386 = lean_ctor_get(x_379, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_379);
x_387 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_385);
lean_ctor_set(x_1, 0, x_387);
x_388 = lean_array_set(x_11, x_25, x_1);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_10);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_386);
return x_390;
}
}
else
{
uint8_t x_391; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_391 = !lean_is_exclusive(x_379);
if (x_391 == 0)
{
return x_379;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_379, 0);
x_393 = lean_ctor_get(x_379, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_379);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_1);
x_395 = l_Lean_Syntax_inhabited;
x_396 = lean_array_get(x_395, x_11, x_25);
x_397 = l_Lean_Syntax_getArgs(x_396);
lean_dec(x_396);
x_398 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_399 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_397, x_398, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_397);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
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
x_403 = l_Lean_nullKind;
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_400);
x_405 = lean_array_set(x_11, x_25, x_404);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_10);
lean_ctor_set(x_406, 1, x_405);
if (lean_is_scalar(x_402)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_402;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_401);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_11);
lean_dec(x_10);
x_408 = lean_ctor_get(x_399, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_399, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_410 = x_399;
} else {
 lean_dec_ref(x_399);
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
else
{
uint8_t x_412; 
lean_free_object(x_27);
x_412 = !lean_is_exclusive(x_1);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_413 = lean_ctor_get(x_1, 1);
lean_dec(x_413);
x_414 = lean_ctor_get(x_1, 0);
lean_dec(x_414);
x_415 = l_Lean_Syntax_inhabited;
x_416 = lean_unsigned_to_nat(0u);
x_417 = lean_array_get(x_415, x_11, x_416);
x_418 = lean_array_get(x_415, x_11, x_25);
x_419 = l_Lean_Syntax_getArgs(x_418);
lean_dec(x_418);
x_420 = l_Lean_mkAppStx___closed__6;
lean_inc(x_3);
x_421 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_420, x_419, x_416, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_423 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_424 = l___private_Lean_Elab_Match_16__processIdAux(x_417, x_423, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_422);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = x_419;
x_428 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed), 11, 3);
lean_closure_set(x_428, 0, x_425);
lean_closure_set(x_428, 1, x_416);
lean_closure_set(x_428, 2, x_427);
x_429 = x_428;
x_430 = lean_apply_8(x_429, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_426);
if (lean_obj_tag(x_430) == 0)
{
uint8_t x_431; 
x_431 = !lean_is_exclusive(x_430);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_430, 0);
x_433 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_432);
lean_ctor_set(x_1, 0, x_433);
x_434 = lean_array_set(x_11, x_25, x_1);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_10);
lean_ctor_set(x_435, 1, x_434);
lean_ctor_set(x_430, 0, x_435);
return x_430;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_ctor_get(x_430, 0);
x_437 = lean_ctor_get(x_430, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_430);
x_438 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_436);
lean_ctor_set(x_1, 0, x_438);
x_439 = lean_array_set(x_11, x_25, x_1);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_10);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_437);
return x_441;
}
}
else
{
uint8_t x_442; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_442 = !lean_is_exclusive(x_430);
if (x_442 == 0)
{
return x_430;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_430, 0);
x_444 = lean_ctor_get(x_430, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_430);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_419);
lean_free_object(x_1);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_446 = !lean_is_exclusive(x_424);
if (x_446 == 0)
{
return x_424;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_424, 0);
x_448 = lean_ctor_get(x_424, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_424);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_419);
lean_dec(x_417);
lean_free_object(x_1);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_450 = !lean_is_exclusive(x_421);
if (x_450 == 0)
{
return x_421;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_421, 0);
x_452 = lean_ctor_get(x_421, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_421);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_1);
x_454 = l_Lean_Syntax_inhabited;
x_455 = lean_unsigned_to_nat(0u);
x_456 = lean_array_get(x_454, x_11, x_455);
x_457 = lean_array_get(x_454, x_11, x_25);
x_458 = l_Lean_Syntax_getArgs(x_457);
lean_dec(x_457);
x_459 = l_Lean_mkAppStx___closed__6;
lean_inc(x_3);
x_460 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_459, x_458, x_455, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; uint8_t x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_463 = l___private_Lean_Elab_Match_16__processIdAux(x_456, x_462, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_461);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = x_458;
x_467 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed), 11, 3);
lean_closure_set(x_467, 0, x_464);
lean_closure_set(x_467, 1, x_455);
lean_closure_set(x_467, 2, x_466);
x_468 = x_467;
x_469 = lean_apply_8(x_468, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_465);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
x_473 = l_Lean_nullKind;
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_470);
x_475 = lean_array_set(x_11, x_25, x_474);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_10);
lean_ctor_set(x_476, 1, x_475);
if (lean_is_scalar(x_472)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_472;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_471);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_11);
lean_dec(x_10);
x_478 = lean_ctor_get(x_469, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_469, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_480 = x_469;
} else {
 lean_dec_ref(x_469);
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
lean_dec(x_458);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_482 = lean_ctor_get(x_463, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_463, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_484 = x_463;
} else {
 lean_dec_ref(x_463);
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
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_486 = lean_ctor_get(x_460, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_460, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_488 = x_460;
} else {
 lean_dec_ref(x_460);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_486);
lean_ctor_set(x_489, 1, x_487);
return x_489;
}
}
}
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; lean_object* x_500; 
x_490 = lean_ctor_get(x_3, 0);
x_491 = lean_ctor_get(x_3, 1);
x_492 = lean_ctor_get(x_3, 2);
x_493 = lean_ctor_get(x_3, 3);
x_494 = lean_ctor_get(x_3, 4);
x_495 = lean_ctor_get(x_3, 5);
x_496 = lean_ctor_get(x_3, 6);
x_497 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_498 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_499 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_inc(x_496);
lean_inc(x_495);
lean_inc(x_494);
lean_inc(x_493);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_3);
x_500 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_500, 0, x_490);
lean_ctor_set(x_500, 1, x_491);
lean_ctor_set(x_500, 2, x_492);
lean_ctor_set(x_500, 3, x_493);
lean_ctor_set(x_500, 4, x_494);
lean_ctor_set(x_500, 5, x_495);
lean_ctor_set(x_500, 6, x_496);
lean_ctor_set(x_500, 7, x_24);
lean_ctor_set_uint8(x_500, sizeof(void*)*8, x_497);
lean_ctor_set_uint8(x_500, sizeof(void*)*8 + 1, x_498);
lean_ctor_set_uint8(x_500, sizeof(void*)*8 + 2, x_499);
if (x_20 == 0)
{
lean_object* x_501; uint8_t x_502; 
x_501 = l___private_Lean_Elab_Match_20__collect___main___closed__2;
x_502 = lean_name_eq(x_10, x_501);
if (x_502 == 0)
{
lean_object* x_503; uint8_t x_504; 
x_503 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_504 = lean_name_eq(x_10, x_503);
if (x_504 == 0)
{
lean_object* x_505; uint8_t x_506; 
x_505 = l_Lean_mkHole___closed__2;
x_506 = lean_name_eq(x_10, x_505);
if (x_506 == 0)
{
lean_object* x_507; uint8_t x_508; 
x_507 = l___private_Lean_Elab_Term_5__hasCDot___main___closed__1;
x_508 = lean_name_eq(x_10, x_507);
if (x_508 == 0)
{
lean_object* x_509; uint8_t x_510; 
lean_dec(x_11);
x_509 = l___private_Lean_Elab_Match_20__collect___main___closed__4;
x_510 = lean_name_eq(x_10, x_509);
if (x_510 == 0)
{
lean_object* x_511; uint8_t x_512; 
x_511 = l___private_Lean_Elab_Match_20__collect___main___closed__5;
x_512 = lean_name_eq(x_10, x_511);
if (x_512 == 0)
{
lean_object* x_513; uint8_t x_514; 
x_513 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_514 = lean_name_eq(x_10, x_513);
if (x_514 == 0)
{
lean_object* x_515; uint8_t x_516; 
x_515 = l_Lean_strLitKind;
x_516 = lean_name_eq(x_10, x_515);
if (x_516 == 0)
{
lean_object* x_517; uint8_t x_518; 
x_517 = l_Lean_numLitKind;
x_518 = lean_name_eq(x_10, x_517);
if (x_518 == 0)
{
lean_object* x_519; uint8_t x_520; 
x_519 = l_Lean_charLitKind;
x_520 = lean_name_eq(x_10, x_519);
if (x_520 == 0)
{
lean_object* x_521; uint8_t x_522; 
lean_free_object(x_27);
lean_dec(x_1);
x_521 = l_Lean_choiceKind;
x_522 = lean_name_eq(x_10, x_521);
lean_dec(x_10);
if (x_522 == 0)
{
lean_object* x_523; 
x_523 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_523;
}
else
{
lean_object* x_524; lean_object* x_525; 
x_524 = l___private_Lean_Elab_Match_20__collect___main___closed__8;
x_525 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_524, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_525;
}
}
else
{
lean_dec(x_500);
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
lean_dec(x_500);
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
lean_dec(x_500);
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
lean_dec(x_500);
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
lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; 
lean_free_object(x_27);
lean_dec(x_10);
x_526 = lean_unsigned_to_nat(0u);
x_527 = l_Lean_Syntax_getArg(x_1, x_526);
x_528 = l_Lean_Syntax_getId(x_527);
x_529 = 0;
lean_inc(x_500);
x_530 = l___private_Lean_Elab_Match_15__processVar(x_528, x_529, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
lean_dec(x_530);
x_532 = lean_unsigned_to_nat(2u);
x_533 = l_Lean_Syntax_getArg(x_1, x_532);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_534 = x_1;
} else {
 lean_dec_ref(x_1);
 x_534 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_500);
x_535 = l___private_Lean_Elab_Match_20__collect___main(x_533, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_531);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = l_Lean_Elab_Term_getCurrMacroScope(x_500, x_4, x_5, x_6, x_7, x_8, x_537);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_500);
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_540);
lean_dec(x_8);
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
x_545 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_546 = l_Lean_addMacroScope(x_542, x_545, x_539);
x_547 = l_Lean_SourceInfo_inhabited___closed__1;
x_548 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_549 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_550 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
lean_ctor_set(x_550, 2, x_546);
lean_ctor_set(x_550, 3, x_549);
x_551 = l_Array_empty___closed__1;
x_552 = lean_array_push(x_551, x_550);
x_553 = lean_array_push(x_551, x_527);
x_554 = lean_array_push(x_553, x_536);
x_555 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_534)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_534;
}
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_554);
x_557 = lean_array_push(x_552, x_556);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_12);
lean_ctor_set(x_558, 1, x_557);
if (lean_is_scalar(x_544)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_544;
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_543);
return x_559;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_534);
lean_dec(x_527);
lean_dec(x_500);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_560 = lean_ctor_get(x_535, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_535, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_562 = x_535;
} else {
 lean_dec_ref(x_535);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_560);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_527);
lean_dec(x_500);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_564 = lean_ctor_get(x_530, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_530, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_566 = x_530;
} else {
 lean_dec_ref(x_530);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_564);
lean_ctor_set(x_567, 1, x_565);
return x_567;
}
}
}
else
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; 
lean_free_object(x_27);
lean_dec(x_10);
x_568 = lean_unsigned_to_nat(0u);
x_569 = l_Lean_Syntax_getArg(x_1, x_568);
x_570 = 1;
x_571 = l___private_Lean_Elab_Match_16__processIdAux(x_569, x_570, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_2);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_573 = x_571;
} else {
 lean_dec_ref(x_571);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_1);
lean_ctor_set(x_574, 1, x_572);
return x_574;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_1);
x_575 = lean_ctor_get(x_571, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_577 = x_571;
} else {
 lean_dec_ref(x_571);
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
}
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_579 = l_Lean_Syntax_inhabited;
x_580 = lean_array_get(x_579, x_11, x_25);
x_581 = l_Lean_Syntax_isNone(x_580);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_582 = x_1;
} else {
 lean_dec_ref(x_1);
 x_582 = lean_box(0);
}
x_583 = lean_unsigned_to_nat(0u);
x_584 = l_Lean_Syntax_getArg(x_580, x_583);
x_585 = l_Lean_Syntax_getArg(x_580, x_25);
x_586 = l_Lean_Syntax_isNone(x_585);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; uint8_t x_589; 
x_587 = l_Lean_Syntax_getArg(x_585, x_583);
x_588 = l_Lean_Elab_Term_elabParen___closed__7;
lean_inc(x_587);
x_589 = l_Lean_Syntax_isOfKind(x_587, x_588);
if (x_589 == 0)
{
lean_object* x_590; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_500);
lean_inc(x_2);
x_590 = l___private_Lean_Elab_Match_20__collect___main(x_584, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = l_Lean_Syntax_setArg(x_580, x_583, x_591);
x_594 = l_Lean_Syntax_getArg(x_587, x_25);
x_595 = l_Lean_Syntax_getArgs(x_594);
lean_dec(x_594);
x_596 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_597 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_595, x_596, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_592);
lean_dec(x_595);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_600 = x_597;
} else {
 lean_dec_ref(x_597);
 x_600 = lean_box(0);
}
x_601 = l_Lean_nullKind;
if (lean_is_scalar(x_582)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_582;
}
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_598);
x_603 = l_Lean_Syntax_setArg(x_587, x_25, x_602);
x_604 = l_Lean_Syntax_setArg(x_585, x_583, x_603);
x_605 = l_Lean_Syntax_setArg(x_593, x_25, x_604);
x_606 = lean_array_set(x_11, x_25, x_605);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_10);
lean_ctor_set(x_607, 1, x_606);
if (lean_is_scalar(x_600)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_600;
}
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_599);
return x_608;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_593);
lean_dec(x_587);
lean_dec(x_585);
lean_dec(x_582);
lean_dec(x_11);
lean_dec(x_10);
x_609 = lean_ctor_get(x_597, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_597, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_611 = x_597;
} else {
 lean_dec_ref(x_597);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_587);
lean_dec(x_585);
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_500);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_613 = lean_ctor_get(x_590, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_590, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_615 = x_590;
} else {
 lean_dec_ref(x_590);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
else
{
lean_object* x_617; 
lean_dec(x_587);
lean_dec(x_585);
x_617 = l___private_Lean_Elab_Match_20__collect___main(x_584, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_620 = x_617;
} else {
 lean_dec_ref(x_617);
 x_620 = lean_box(0);
}
x_621 = l_Lean_Syntax_setArg(x_580, x_583, x_618);
x_622 = lean_array_set(x_11, x_25, x_621);
if (lean_is_scalar(x_582)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_582;
}
lean_ctor_set(x_623, 0, x_10);
lean_ctor_set(x_623, 1, x_622);
if (lean_is_scalar(x_620)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_620;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_619);
return x_624;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_11);
lean_dec(x_10);
x_625 = lean_ctor_get(x_617, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_617, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_627 = x_617;
} else {
 lean_dec_ref(x_617);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
}
else
{
lean_object* x_629; 
lean_dec(x_585);
x_629 = l___private_Lean_Elab_Match_20__collect___main(x_584, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_632 = x_629;
} else {
 lean_dec_ref(x_629);
 x_632 = lean_box(0);
}
x_633 = l_Lean_Syntax_setArg(x_580, x_583, x_630);
x_634 = lean_array_set(x_11, x_25, x_633);
if (lean_is_scalar(x_582)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_582;
}
lean_ctor_set(x_635, 0, x_10);
lean_ctor_set(x_635, 1, x_634);
if (lean_is_scalar(x_632)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_632;
}
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_631);
return x_636;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_11);
lean_dec(x_10);
x_637 = lean_ctor_get(x_629, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_629, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_639 = x_629;
} else {
 lean_dec_ref(x_629);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_639)) {
 x_640 = lean_alloc_ctor(1, 2, 0);
} else {
 x_640 = x_639;
}
lean_ctor_set(x_640, 0, x_637);
lean_ctor_set(x_640, 1, x_638);
return x_640;
}
}
}
else
{
lean_dec(x_580);
lean_dec(x_500);
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
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_500);
lean_free_object(x_27);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_641 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_29);
lean_dec(x_8);
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_644 = lean_st_ref_take(x_2, x_643);
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
x_647 = lean_ctor_get(x_645, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_645, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_649 = x_645;
} else {
 lean_dec_ref(x_645);
 x_649 = lean_box(0);
}
x_650 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_642);
x_651 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_651, 0, x_650);
x_652 = lean_array_push(x_648, x_651);
if (lean_is_scalar(x_649)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_649;
}
lean_ctor_set(x_653, 0, x_647);
lean_ctor_set(x_653, 1, x_652);
x_654 = lean_st_ref_set(x_2, x_653, x_646);
lean_dec(x_2);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_642);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_658 = x_1;
} else {
 lean_dec_ref(x_1);
 x_658 = lean_box(0);
}
x_659 = l_Lean_Syntax_inhabited;
x_660 = lean_array_get(x_659, x_11, x_25);
x_661 = l_Lean_Syntax_isNone(x_660);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_658);
lean_dec(x_11);
lean_dec(x_10);
x_662 = l___private_Lean_Elab_Match_20__collect___main___closed__17;
x_663 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_660, x_662, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_660);
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
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_664);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_660);
x_668 = lean_unsigned_to_nat(2u);
x_669 = lean_array_get(x_659, x_11, x_668);
x_670 = l_Lean_Syntax_getArgs(x_669);
lean_dec(x_669);
x_671 = l___private_Lean_Elab_Match_20__collect___main___closed__18;
x_672 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_670, x_671, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_670);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_672)) {
 lean_ctor_release(x_672, 0);
 lean_ctor_release(x_672, 1);
 x_675 = x_672;
} else {
 lean_dec_ref(x_672);
 x_675 = lean_box(0);
}
x_676 = l_Lean_nullKind;
if (lean_is_scalar(x_658)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_658;
}
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_673);
x_678 = lean_array_set(x_11, x_668, x_677);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_10);
lean_ctor_set(x_679, 1, x_678);
if (lean_is_scalar(x_675)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_675;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_674);
return x_680;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_658);
lean_dec(x_11);
lean_dec(x_10);
x_681 = lean_ctor_get(x_672, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_672, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_672)) {
 lean_ctor_release(x_672, 0);
 lean_ctor_release(x_672, 1);
 x_683 = x_672;
} else {
 lean_dec_ref(x_672);
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
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_685 = x_1;
} else {
 lean_dec_ref(x_1);
 x_685 = lean_box(0);
}
x_686 = l_Lean_Syntax_inhabited;
x_687 = lean_array_get(x_686, x_11, x_25);
x_688 = l_Lean_Syntax_getArgs(x_687);
lean_dec(x_687);
x_689 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_690 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_688, x_689, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_688);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
x_694 = l_Lean_nullKind;
if (lean_is_scalar(x_685)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_685;
}
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_691);
x_696 = lean_array_set(x_11, x_25, x_695);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_10);
lean_ctor_set(x_697, 1, x_696);
if (lean_is_scalar(x_693)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_693;
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_692);
return x_698;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_685);
lean_dec(x_11);
lean_dec(x_10);
x_699 = lean_ctor_get(x_690, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_690, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_701 = x_690;
} else {
 lean_dec_ref(x_690);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
return x_702;
}
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_free_object(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_703 = x_1;
} else {
 lean_dec_ref(x_1);
 x_703 = lean_box(0);
}
x_704 = l_Lean_Syntax_inhabited;
x_705 = lean_unsigned_to_nat(0u);
x_706 = lean_array_get(x_704, x_11, x_705);
x_707 = lean_array_get(x_704, x_11, x_25);
x_708 = l_Lean_Syntax_getArgs(x_707);
lean_dec(x_707);
x_709 = l_Lean_mkAppStx___closed__6;
lean_inc(x_500);
x_710 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_709, x_708, x_705, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; uint8_t x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
x_712 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_500);
x_713 = l___private_Lean_Elab_Match_16__processIdAux(x_706, x_712, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_711);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = x_708;
x_717 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed), 11, 3);
lean_closure_set(x_717, 0, x_714);
lean_closure_set(x_717, 1, x_705);
lean_closure_set(x_717, 2, x_716);
x_718 = x_717;
x_719 = lean_apply_8(x_718, x_2, x_500, x_4, x_5, x_6, x_7, x_8, x_715);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_722 = x_719;
} else {
 lean_dec_ref(x_719);
 x_722 = lean_box(0);
}
x_723 = l_Lean_nullKind;
if (lean_is_scalar(x_703)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_703;
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_720);
x_725 = lean_array_set(x_11, x_25, x_724);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_10);
lean_ctor_set(x_726, 1, x_725);
if (lean_is_scalar(x_722)) {
 x_727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_727 = x_722;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_721);
return x_727;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
lean_dec(x_703);
lean_dec(x_11);
lean_dec(x_10);
x_728 = lean_ctor_get(x_719, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_719, 1);
lean_inc(x_729);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_730 = x_719;
} else {
 lean_dec_ref(x_719);
 x_730 = lean_box(0);
}
if (lean_is_scalar(x_730)) {
 x_731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_731 = x_730;
}
lean_ctor_set(x_731, 0, x_728);
lean_ctor_set(x_731, 1, x_729);
return x_731;
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_708);
lean_dec(x_703);
lean_dec(x_500);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_732 = lean_ctor_get(x_713, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_713, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 lean_ctor_release(x_713, 1);
 x_734 = x_713;
} else {
 lean_dec_ref(x_713);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(1, 2, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_732);
lean_ctor_set(x_735, 1, x_733);
return x_735;
}
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_703);
lean_dec(x_500);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_736 = lean_ctor_get(x_710, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_710, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_738 = x_710;
} else {
 lean_dec_ref(x_710);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_736);
lean_ctor_set(x_739, 1, x_737);
return x_739;
}
}
}
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; uint8_t x_749; uint8_t x_750; lean_object* x_751; lean_object* x_752; 
x_740 = lean_ctor_get(x_27, 1);
lean_inc(x_740);
lean_dec(x_27);
x_741 = lean_ctor_get(x_3, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_3, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_3, 2);
lean_inc(x_743);
x_744 = lean_ctor_get(x_3, 3);
lean_inc(x_744);
x_745 = lean_ctor_get(x_3, 4);
lean_inc(x_745);
x_746 = lean_ctor_get(x_3, 5);
lean_inc(x_746);
x_747 = lean_ctor_get(x_3, 6);
lean_inc(x_747);
x_748 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_749 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_750 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_751 = x_3;
} else {
 lean_dec_ref(x_3);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(0, 8, 3);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_741);
lean_ctor_set(x_752, 1, x_742);
lean_ctor_set(x_752, 2, x_743);
lean_ctor_set(x_752, 3, x_744);
lean_ctor_set(x_752, 4, x_745);
lean_ctor_set(x_752, 5, x_746);
lean_ctor_set(x_752, 6, x_747);
lean_ctor_set(x_752, 7, x_24);
lean_ctor_set_uint8(x_752, sizeof(void*)*8, x_748);
lean_ctor_set_uint8(x_752, sizeof(void*)*8 + 1, x_749);
lean_ctor_set_uint8(x_752, sizeof(void*)*8 + 2, x_750);
if (x_20 == 0)
{
lean_object* x_753; uint8_t x_754; 
x_753 = l___private_Lean_Elab_Match_20__collect___main___closed__2;
x_754 = lean_name_eq(x_10, x_753);
if (x_754 == 0)
{
lean_object* x_755; uint8_t x_756; 
x_755 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_756 = lean_name_eq(x_10, x_755);
if (x_756 == 0)
{
lean_object* x_757; uint8_t x_758; 
x_757 = l_Lean_mkHole___closed__2;
x_758 = lean_name_eq(x_10, x_757);
if (x_758 == 0)
{
lean_object* x_759; uint8_t x_760; 
x_759 = l___private_Lean_Elab_Term_5__hasCDot___main___closed__1;
x_760 = lean_name_eq(x_10, x_759);
if (x_760 == 0)
{
lean_object* x_761; uint8_t x_762; 
lean_dec(x_11);
x_761 = l___private_Lean_Elab_Match_20__collect___main___closed__4;
x_762 = lean_name_eq(x_10, x_761);
if (x_762 == 0)
{
lean_object* x_763; uint8_t x_764; 
x_763 = l___private_Lean_Elab_Match_20__collect___main___closed__5;
x_764 = lean_name_eq(x_10, x_763);
if (x_764 == 0)
{
lean_object* x_765; uint8_t x_766; 
x_765 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_766 = lean_name_eq(x_10, x_765);
if (x_766 == 0)
{
lean_object* x_767; uint8_t x_768; 
x_767 = l_Lean_strLitKind;
x_768 = lean_name_eq(x_10, x_767);
if (x_768 == 0)
{
lean_object* x_769; uint8_t x_770; 
x_769 = l_Lean_numLitKind;
x_770 = lean_name_eq(x_10, x_769);
if (x_770 == 0)
{
lean_object* x_771; uint8_t x_772; 
x_771 = l_Lean_charLitKind;
x_772 = lean_name_eq(x_10, x_771);
if (x_772 == 0)
{
lean_object* x_773; uint8_t x_774; 
lean_dec(x_1);
x_773 = l_Lean_choiceKind;
x_774 = lean_name_eq(x_10, x_773);
lean_dec(x_10);
if (x_774 == 0)
{
lean_object* x_775; 
x_775 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_775;
}
else
{
lean_object* x_776; lean_object* x_777; 
x_776 = l___private_Lean_Elab_Match_20__collect___main___closed__8;
x_777 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_776, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_777;
}
}
else
{
lean_object* x_778; 
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_1);
lean_ctor_set(x_778, 1, x_740);
return x_778;
}
}
else
{
lean_object* x_779; 
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_779 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_779, 0, x_1);
lean_ctor_set(x_779, 1, x_740);
return x_779;
}
}
else
{
lean_object* x_780; 
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_780, 0, x_1);
lean_ctor_set(x_780, 1, x_740);
return x_780;
}
}
else
{
lean_object* x_781; 
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_781 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_781, 0, x_1);
lean_ctor_set(x_781, 1, x_740);
return x_781;
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; uint8_t x_785; lean_object* x_786; 
lean_dec(x_10);
x_782 = lean_unsigned_to_nat(0u);
x_783 = l_Lean_Syntax_getArg(x_1, x_782);
x_784 = l_Lean_Syntax_getId(x_783);
x_785 = 0;
lean_inc(x_752);
x_786 = l___private_Lean_Elab_Match_15__processVar(x_784, x_785, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_787 = lean_ctor_get(x_786, 1);
lean_inc(x_787);
lean_dec(x_786);
x_788 = lean_unsigned_to_nat(2u);
x_789 = l_Lean_Syntax_getArg(x_1, x_788);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_790 = x_1;
} else {
 lean_dec_ref(x_1);
 x_790 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_752);
x_791 = l___private_Lean_Elab_Match_20__collect___main(x_789, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_787);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
x_794 = l_Lean_Elab_Term_getCurrMacroScope(x_752, x_4, x_5, x_6, x_7, x_8, x_793);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_752);
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_796);
lean_dec(x_8);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_800 = x_797;
} else {
 lean_dec_ref(x_797);
 x_800 = lean_box(0);
}
x_801 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_802 = l_Lean_addMacroScope(x_798, x_801, x_795);
x_803 = l_Lean_SourceInfo_inhabited___closed__1;
x_804 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_805 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_806 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_806, 0, x_803);
lean_ctor_set(x_806, 1, x_804);
lean_ctor_set(x_806, 2, x_802);
lean_ctor_set(x_806, 3, x_805);
x_807 = l_Array_empty___closed__1;
x_808 = lean_array_push(x_807, x_806);
x_809 = lean_array_push(x_807, x_783);
x_810 = lean_array_push(x_809, x_792);
x_811 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_790)) {
 x_812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_812 = x_790;
}
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_810);
x_813 = lean_array_push(x_808, x_812);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_12);
lean_ctor_set(x_814, 1, x_813);
if (lean_is_scalar(x_800)) {
 x_815 = lean_alloc_ctor(0, 2, 0);
} else {
 x_815 = x_800;
}
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_799);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_790);
lean_dec(x_783);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_816 = lean_ctor_get(x_791, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_791, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_818 = x_791;
} else {
 lean_dec_ref(x_791);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(1, 2, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_816);
lean_ctor_set(x_819, 1, x_817);
return x_819;
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_783);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_820 = lean_ctor_get(x_786, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_786, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_822 = x_786;
} else {
 lean_dec_ref(x_786);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_820);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
}
}
else
{
lean_object* x_824; lean_object* x_825; uint8_t x_826; lean_object* x_827; 
lean_dec(x_10);
x_824 = lean_unsigned_to_nat(0u);
x_825 = l_Lean_Syntax_getArg(x_1, x_824);
x_826 = 1;
x_827 = l___private_Lean_Elab_Match_16__processIdAux(x_825, x_826, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
lean_dec(x_2);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_829 = x_827;
} else {
 lean_dec_ref(x_827);
 x_829 = lean_box(0);
}
if (lean_is_scalar(x_829)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_829;
}
lean_ctor_set(x_830, 0, x_1);
lean_ctor_set(x_830, 1, x_828);
return x_830;
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_1);
x_831 = lean_ctor_get(x_827, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_827, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_833 = x_827;
} else {
 lean_dec_ref(x_827);
 x_833 = lean_box(0);
}
if (lean_is_scalar(x_833)) {
 x_834 = lean_alloc_ctor(1, 2, 0);
} else {
 x_834 = x_833;
}
lean_ctor_set(x_834, 0, x_831);
lean_ctor_set(x_834, 1, x_832);
return x_834;
}
}
}
else
{
lean_object* x_835; lean_object* x_836; uint8_t x_837; 
x_835 = l_Lean_Syntax_inhabited;
x_836 = lean_array_get(x_835, x_11, x_25);
x_837 = l_Lean_Syntax_isNone(x_836);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_838 = x_1;
} else {
 lean_dec_ref(x_1);
 x_838 = lean_box(0);
}
x_839 = lean_unsigned_to_nat(0u);
x_840 = l_Lean_Syntax_getArg(x_836, x_839);
x_841 = l_Lean_Syntax_getArg(x_836, x_25);
x_842 = l_Lean_Syntax_isNone(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; uint8_t x_845; 
x_843 = l_Lean_Syntax_getArg(x_841, x_839);
x_844 = l_Lean_Elab_Term_elabParen___closed__7;
lean_inc(x_843);
x_845 = l_Lean_Syntax_isOfKind(x_843, x_844);
if (x_845 == 0)
{
lean_object* x_846; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_752);
lean_inc(x_2);
x_846 = l___private_Lean_Elab_Match_20__collect___main(x_840, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_847 = lean_ctor_get(x_846, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_846, 1);
lean_inc(x_848);
lean_dec(x_846);
x_849 = l_Lean_Syntax_setArg(x_836, x_839, x_847);
x_850 = l_Lean_Syntax_getArg(x_843, x_25);
x_851 = l_Lean_Syntax_getArgs(x_850);
lean_dec(x_850);
x_852 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_853 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_851, x_852, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_848);
lean_dec(x_851);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_856 = x_853;
} else {
 lean_dec_ref(x_853);
 x_856 = lean_box(0);
}
x_857 = l_Lean_nullKind;
if (lean_is_scalar(x_838)) {
 x_858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_858 = x_838;
}
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_854);
x_859 = l_Lean_Syntax_setArg(x_843, x_25, x_858);
x_860 = l_Lean_Syntax_setArg(x_841, x_839, x_859);
x_861 = l_Lean_Syntax_setArg(x_849, x_25, x_860);
x_862 = lean_array_set(x_11, x_25, x_861);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_10);
lean_ctor_set(x_863, 1, x_862);
if (lean_is_scalar(x_856)) {
 x_864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_864 = x_856;
}
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_855);
return x_864;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_849);
lean_dec(x_843);
lean_dec(x_841);
lean_dec(x_838);
lean_dec(x_11);
lean_dec(x_10);
x_865 = lean_ctor_get(x_853, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_853, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_867 = x_853;
} else {
 lean_dec_ref(x_853);
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
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_843);
lean_dec(x_841);
lean_dec(x_838);
lean_dec(x_836);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_869 = lean_ctor_get(x_846, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_846, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 x_871 = x_846;
} else {
 lean_dec_ref(x_846);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_870);
return x_872;
}
}
else
{
lean_object* x_873; 
lean_dec(x_843);
lean_dec(x_841);
x_873 = l___private_Lean_Elab_Match_20__collect___main(x_840, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_876 = x_873;
} else {
 lean_dec_ref(x_873);
 x_876 = lean_box(0);
}
x_877 = l_Lean_Syntax_setArg(x_836, x_839, x_874);
x_878 = lean_array_set(x_11, x_25, x_877);
if (lean_is_scalar(x_838)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_838;
}
lean_ctor_set(x_879, 0, x_10);
lean_ctor_set(x_879, 1, x_878);
if (lean_is_scalar(x_876)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_876;
}
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_875);
return x_880;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_838);
lean_dec(x_836);
lean_dec(x_11);
lean_dec(x_10);
x_881 = lean_ctor_get(x_873, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_873, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_883 = x_873;
} else {
 lean_dec_ref(x_873);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_882);
return x_884;
}
}
}
else
{
lean_object* x_885; 
lean_dec(x_841);
x_885 = l___private_Lean_Elab_Match_20__collect___main(x_840, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_888 = x_885;
} else {
 lean_dec_ref(x_885);
 x_888 = lean_box(0);
}
x_889 = l_Lean_Syntax_setArg(x_836, x_839, x_886);
x_890 = lean_array_set(x_11, x_25, x_889);
if (lean_is_scalar(x_838)) {
 x_891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_891 = x_838;
}
lean_ctor_set(x_891, 0, x_10);
lean_ctor_set(x_891, 1, x_890);
if (lean_is_scalar(x_888)) {
 x_892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_892 = x_888;
}
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_887);
return x_892;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_838);
lean_dec(x_836);
lean_dec(x_11);
lean_dec(x_10);
x_893 = lean_ctor_get(x_885, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_885, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_895 = x_885;
} else {
 lean_dec_ref(x_885);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
}
else
{
lean_object* x_897; 
lean_dec(x_836);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_897, 0, x_1);
lean_ctor_set(x_897, 1, x_740);
return x_897;
}
}
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_898 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_740);
lean_dec(x_8);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
lean_dec(x_898);
x_901 = lean_st_ref_take(x_2, x_900);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
lean_dec(x_901);
x_904 = lean_ctor_get(x_902, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_902, 1);
lean_inc(x_905);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_906 = x_902;
} else {
 lean_dec_ref(x_902);
 x_906 = lean_box(0);
}
x_907 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_899);
x_908 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_908, 0, x_907);
x_909 = lean_array_push(x_905, x_908);
if (lean_is_scalar(x_906)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_906;
}
lean_ctor_set(x_910, 0, x_904);
lean_ctor_set(x_910, 1, x_909);
x_911 = lean_st_ref_set(x_2, x_910, x_903);
lean_dec(x_2);
x_912 = lean_ctor_get(x_911, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_913 = x_911;
} else {
 lean_dec_ref(x_911);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_899);
lean_ctor_set(x_914, 1, x_912);
return x_914;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; uint8_t x_918; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_915 = x_1;
} else {
 lean_dec_ref(x_1);
 x_915 = lean_box(0);
}
x_916 = l_Lean_Syntax_inhabited;
x_917 = lean_array_get(x_916, x_11, x_25);
x_918 = l_Lean_Syntax_isNone(x_917);
if (x_918 == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_915);
lean_dec(x_11);
lean_dec(x_10);
x_919 = l___private_Lean_Elab_Match_20__collect___main___closed__17;
x_920 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_917, x_919, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_917);
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_923 = x_920;
} else {
 lean_dec_ref(x_920);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_921);
lean_ctor_set(x_924, 1, x_922);
return x_924;
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_dec(x_917);
x_925 = lean_unsigned_to_nat(2u);
x_926 = lean_array_get(x_916, x_11, x_925);
x_927 = l_Lean_Syntax_getArgs(x_926);
lean_dec(x_926);
x_928 = l___private_Lean_Elab_Match_20__collect___main___closed__18;
x_929 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_927, x_928, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
lean_dec(x_927);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
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
x_933 = l_Lean_nullKind;
if (lean_is_scalar(x_915)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_915;
}
lean_ctor_set(x_934, 0, x_933);
lean_ctor_set(x_934, 1, x_930);
x_935 = lean_array_set(x_11, x_925, x_934);
x_936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_936, 0, x_10);
lean_ctor_set(x_936, 1, x_935);
if (lean_is_scalar(x_932)) {
 x_937 = lean_alloc_ctor(0, 2, 0);
} else {
 x_937 = x_932;
}
lean_ctor_set(x_937, 0, x_936);
lean_ctor_set(x_937, 1, x_931);
return x_937;
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_915);
lean_dec(x_11);
lean_dec(x_10);
x_938 = lean_ctor_get(x_929, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_929, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_940 = x_929;
} else {
 lean_dec_ref(x_929);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_938);
lean_ctor_set(x_941, 1, x_939);
return x_941;
}
}
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_942 = x_1;
} else {
 lean_dec_ref(x_1);
 x_942 = lean_box(0);
}
x_943 = l_Lean_Syntax_inhabited;
x_944 = lean_array_get(x_943, x_11, x_25);
x_945 = l_Lean_Syntax_getArgs(x_944);
lean_dec(x_944);
x_946 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_947 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_945, x_946, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
lean_dec(x_945);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_950 = x_947;
} else {
 lean_dec_ref(x_947);
 x_950 = lean_box(0);
}
x_951 = l_Lean_nullKind;
if (lean_is_scalar(x_942)) {
 x_952 = lean_alloc_ctor(1, 2, 0);
} else {
 x_952 = x_942;
}
lean_ctor_set(x_952, 0, x_951);
lean_ctor_set(x_952, 1, x_948);
x_953 = lean_array_set(x_11, x_25, x_952);
x_954 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_954, 0, x_10);
lean_ctor_set(x_954, 1, x_953);
if (lean_is_scalar(x_950)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_950;
}
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_949);
return x_955;
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
lean_dec(x_942);
lean_dec(x_11);
lean_dec(x_10);
x_956 = lean_ctor_get(x_947, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_947, 1);
lean_inc(x_957);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_958 = x_947;
} else {
 lean_dec_ref(x_947);
 x_958 = lean_box(0);
}
if (lean_is_scalar(x_958)) {
 x_959 = lean_alloc_ctor(1, 2, 0);
} else {
 x_959 = x_958;
}
lean_ctor_set(x_959, 0, x_956);
lean_ctor_set(x_959, 1, x_957);
return x_959;
}
}
}
else
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_960 = x_1;
} else {
 lean_dec_ref(x_1);
 x_960 = lean_box(0);
}
x_961 = l_Lean_Syntax_inhabited;
x_962 = lean_unsigned_to_nat(0u);
x_963 = lean_array_get(x_961, x_11, x_962);
x_964 = lean_array_get(x_961, x_11, x_25);
x_965 = l_Lean_Syntax_getArgs(x_964);
lean_dec(x_964);
x_966 = l_Lean_mkAppStx___closed__6;
lean_inc(x_752);
x_967 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_966, x_965, x_962, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_740);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; uint8_t x_969; lean_object* x_970; 
x_968 = lean_ctor_get(x_967, 1);
lean_inc(x_968);
lean_dec(x_967);
x_969 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_752);
x_970 = l___private_Lean_Elab_Match_16__processIdAux(x_963, x_969, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_968);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
x_973 = x_965;
x_974 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed), 11, 3);
lean_closure_set(x_974, 0, x_971);
lean_closure_set(x_974, 1, x_962);
lean_closure_set(x_974, 2, x_973);
x_975 = x_974;
x_976 = lean_apply_8(x_975, x_2, x_752, x_4, x_5, x_6, x_7, x_8, x_972);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_979 = x_976;
} else {
 lean_dec_ref(x_976);
 x_979 = lean_box(0);
}
x_980 = l_Lean_nullKind;
if (lean_is_scalar(x_960)) {
 x_981 = lean_alloc_ctor(1, 2, 0);
} else {
 x_981 = x_960;
}
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_977);
x_982 = lean_array_set(x_11, x_25, x_981);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_10);
lean_ctor_set(x_983, 1, x_982);
if (lean_is_scalar(x_979)) {
 x_984 = lean_alloc_ctor(0, 2, 0);
} else {
 x_984 = x_979;
}
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_978);
return x_984;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_960);
lean_dec(x_11);
lean_dec(x_10);
x_985 = lean_ctor_get(x_976, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_976, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_987 = x_976;
} else {
 lean_dec_ref(x_976);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
return x_988;
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec(x_965);
lean_dec(x_960);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_989 = lean_ctor_get(x_970, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_970, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_991 = x_970;
} else {
 lean_dec_ref(x_970);
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
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; 
lean_dec(x_965);
lean_dec(x_963);
lean_dec(x_960);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_993 = lean_ctor_get(x_967, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_967, 1);
lean_inc(x_994);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_995 = x_967;
} else {
 lean_dec_ref(x_967);
 x_995 = lean_box(0);
}
if (lean_is_scalar(x_995)) {
 x_996 = lean_alloc_ctor(1, 2, 0);
} else {
 x_996 = x_995;
}
lean_ctor_set(x_996, 0, x_993);
lean_ctor_set(x_996, 1, x_994);
return x_996;
}
}
}
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; uint8_t x_1017; uint8_t x_1018; uint8_t x_1019; lean_object* x_1020; lean_object* x_1021; 
x_997 = lean_ctor_get(x_21, 0);
x_998 = lean_ctor_get(x_21, 1);
x_999 = lean_ctor_get(x_21, 2);
x_1000 = lean_ctor_get(x_21, 3);
x_1001 = lean_ctor_get(x_21, 4);
x_1002 = lean_ctor_get(x_21, 5);
x_1003 = lean_ctor_get(x_21, 6);
lean_inc(x_1003);
lean_inc(x_1002);
lean_inc(x_1001);
lean_inc(x_1000);
lean_inc(x_999);
lean_inc(x_998);
lean_inc(x_997);
lean_dec(x_21);
x_1004 = lean_unsigned_to_nat(1u);
x_1005 = lean_nat_add(x_1002, x_1004);
x_1006 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1006, 0, x_997);
lean_ctor_set(x_1006, 1, x_998);
lean_ctor_set(x_1006, 2, x_999);
lean_ctor_set(x_1006, 3, x_1000);
lean_ctor_set(x_1006, 4, x_1001);
lean_ctor_set(x_1006, 5, x_1005);
lean_ctor_set(x_1006, 6, x_1003);
x_1007 = lean_st_ref_set(x_4, x_1006, x_22);
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
x_1010 = lean_ctor_get(x_3, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_3, 1);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_3, 2);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_3, 3);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_3, 4);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_3, 5);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_3, 6);
lean_inc(x_1016);
x_1017 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_1018 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_1019 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_1020 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1020 = lean_box(0);
}
if (lean_is_scalar(x_1020)) {
 x_1021 = lean_alloc_ctor(0, 8, 3);
} else {
 x_1021 = x_1020;
}
lean_ctor_set(x_1021, 0, x_1010);
lean_ctor_set(x_1021, 1, x_1011);
lean_ctor_set(x_1021, 2, x_1012);
lean_ctor_set(x_1021, 3, x_1013);
lean_ctor_set(x_1021, 4, x_1014);
lean_ctor_set(x_1021, 5, x_1015);
lean_ctor_set(x_1021, 6, x_1016);
lean_ctor_set(x_1021, 7, x_1002);
lean_ctor_set_uint8(x_1021, sizeof(void*)*8, x_1017);
lean_ctor_set_uint8(x_1021, sizeof(void*)*8 + 1, x_1018);
lean_ctor_set_uint8(x_1021, sizeof(void*)*8 + 2, x_1019);
if (x_20 == 0)
{
lean_object* x_1022; uint8_t x_1023; 
x_1022 = l___private_Lean_Elab_Match_20__collect___main___closed__2;
x_1023 = lean_name_eq(x_10, x_1022);
if (x_1023 == 0)
{
lean_object* x_1024; uint8_t x_1025; 
x_1024 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_1025 = lean_name_eq(x_10, x_1024);
if (x_1025 == 0)
{
lean_object* x_1026; uint8_t x_1027; 
x_1026 = l_Lean_mkHole___closed__2;
x_1027 = lean_name_eq(x_10, x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; uint8_t x_1029; 
x_1028 = l___private_Lean_Elab_Term_5__hasCDot___main___closed__1;
x_1029 = lean_name_eq(x_10, x_1028);
if (x_1029 == 0)
{
lean_object* x_1030; uint8_t x_1031; 
lean_dec(x_11);
x_1030 = l___private_Lean_Elab_Match_20__collect___main___closed__4;
x_1031 = lean_name_eq(x_10, x_1030);
if (x_1031 == 0)
{
lean_object* x_1032; uint8_t x_1033; 
x_1032 = l___private_Lean_Elab_Match_20__collect___main___closed__5;
x_1033 = lean_name_eq(x_10, x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; uint8_t x_1035; 
x_1034 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_1035 = lean_name_eq(x_10, x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; uint8_t x_1037; 
x_1036 = l_Lean_strLitKind;
x_1037 = lean_name_eq(x_10, x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; uint8_t x_1039; 
x_1038 = l_Lean_numLitKind;
x_1039 = lean_name_eq(x_10, x_1038);
if (x_1039 == 0)
{
lean_object* x_1040; uint8_t x_1041; 
x_1040 = l_Lean_charLitKind;
x_1041 = lean_name_eq(x_10, x_1040);
if (x_1041 == 0)
{
lean_object* x_1042; uint8_t x_1043; 
lean_dec(x_1009);
lean_dec(x_1);
x_1042 = l_Lean_choiceKind;
x_1043 = lean_name_eq(x_10, x_1042);
lean_dec(x_10);
if (x_1043 == 0)
{
lean_object* x_1044; 
x_1044 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1044;
}
else
{
lean_object* x_1045; lean_object* x_1046; 
x_1045 = l___private_Lean_Elab_Match_20__collect___main___closed__8;
x_1046 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_1045, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1046;
}
}
else
{
lean_object* x_1047; 
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1009)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1009;
}
lean_ctor_set(x_1047, 0, x_1);
lean_ctor_set(x_1047, 1, x_1008);
return x_1047;
}
}
else
{
lean_object* x_1048; 
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1009)) {
 x_1048 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1048 = x_1009;
}
lean_ctor_set(x_1048, 0, x_1);
lean_ctor_set(x_1048, 1, x_1008);
return x_1048;
}
}
else
{
lean_object* x_1049; 
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1009)) {
 x_1049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1049 = x_1009;
}
lean_ctor_set(x_1049, 0, x_1);
lean_ctor_set(x_1049, 1, x_1008);
return x_1049;
}
}
else
{
lean_object* x_1050; 
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1009)) {
 x_1050 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1050 = x_1009;
}
lean_ctor_set(x_1050, 0, x_1);
lean_ctor_set(x_1050, 1, x_1008);
return x_1050;
}
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; uint8_t x_1054; lean_object* x_1055; 
lean_dec(x_1009);
lean_dec(x_10);
x_1051 = lean_unsigned_to_nat(0u);
x_1052 = l_Lean_Syntax_getArg(x_1, x_1051);
x_1053 = l_Lean_Syntax_getId(x_1052);
x_1054 = 0;
lean_inc(x_1021);
x_1055 = l___private_Lean_Elab_Match_15__processVar(x_1053, x_1054, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1056 = lean_ctor_get(x_1055, 1);
lean_inc(x_1056);
lean_dec(x_1055);
x_1057 = lean_unsigned_to_nat(2u);
x_1058 = l_Lean_Syntax_getArg(x_1, x_1057);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1059 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1059 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1021);
x_1060 = l___private_Lean_Elab_Match_20__collect___main(x_1058, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1056);
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1061 = lean_ctor_get(x_1060, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1060, 1);
lean_inc(x_1062);
lean_dec(x_1060);
x_1063 = l_Lean_Elab_Term_getCurrMacroScope(x_1021, x_4, x_5, x_6, x_7, x_8, x_1062);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1021);
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1065);
lean_dec(x_8);
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1069 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1069 = lean_box(0);
}
x_1070 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_1071 = l_Lean_addMacroScope(x_1067, x_1070, x_1064);
x_1072 = l_Lean_SourceInfo_inhabited___closed__1;
x_1073 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_1074 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_1075 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1075, 0, x_1072);
lean_ctor_set(x_1075, 1, x_1073);
lean_ctor_set(x_1075, 2, x_1071);
lean_ctor_set(x_1075, 3, x_1074);
x_1076 = l_Array_empty___closed__1;
x_1077 = lean_array_push(x_1076, x_1075);
x_1078 = lean_array_push(x_1076, x_1052);
x_1079 = lean_array_push(x_1078, x_1061);
x_1080 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_1059)) {
 x_1081 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1081 = x_1059;
}
lean_ctor_set(x_1081, 0, x_1080);
lean_ctor_set(x_1081, 1, x_1079);
x_1082 = lean_array_push(x_1077, x_1081);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_12);
lean_ctor_set(x_1083, 1, x_1082);
if (lean_is_scalar(x_1069)) {
 x_1084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1084 = x_1069;
}
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1084, 1, x_1068);
return x_1084;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_1059);
lean_dec(x_1052);
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1085 = lean_ctor_get(x_1060, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1060, 1);
lean_inc(x_1086);
if (lean_is_exclusive(x_1060)) {
 lean_ctor_release(x_1060, 0);
 lean_ctor_release(x_1060, 1);
 x_1087 = x_1060;
} else {
 lean_dec_ref(x_1060);
 x_1087 = lean_box(0);
}
if (lean_is_scalar(x_1087)) {
 x_1088 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1088 = x_1087;
}
lean_ctor_set(x_1088, 0, x_1085);
lean_ctor_set(x_1088, 1, x_1086);
return x_1088;
}
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1052);
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1089 = lean_ctor_get(x_1055, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1055, 1);
lean_inc(x_1090);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1091 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1091 = lean_box(0);
}
if (lean_is_scalar(x_1091)) {
 x_1092 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1092 = x_1091;
}
lean_ctor_set(x_1092, 0, x_1089);
lean_ctor_set(x_1092, 1, x_1090);
return x_1092;
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; lean_object* x_1096; 
lean_dec(x_1009);
lean_dec(x_10);
x_1093 = lean_unsigned_to_nat(0u);
x_1094 = l_Lean_Syntax_getArg(x_1, x_1093);
x_1095 = 1;
x_1096 = l___private_Lean_Elab_Match_16__processIdAux(x_1094, x_1095, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
lean_dec(x_2);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1096, 1);
lean_inc(x_1097);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1098 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_1);
lean_ctor_set(x_1099, 1, x_1097);
return x_1099;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1);
x_1100 = lean_ctor_get(x_1096, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1096, 1);
lean_inc(x_1101);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1102 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1101);
return x_1103;
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; uint8_t x_1106; 
x_1104 = l_Lean_Syntax_inhabited;
x_1105 = lean_array_get(x_1104, x_11, x_1004);
x_1106 = l_Lean_Syntax_isNone(x_1105);
if (x_1106 == 0)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
lean_dec(x_1009);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1107 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1107 = lean_box(0);
}
x_1108 = lean_unsigned_to_nat(0u);
x_1109 = l_Lean_Syntax_getArg(x_1105, x_1108);
x_1110 = l_Lean_Syntax_getArg(x_1105, x_1004);
x_1111 = l_Lean_Syntax_isNone(x_1110);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; uint8_t x_1114; 
x_1112 = l_Lean_Syntax_getArg(x_1110, x_1108);
x_1113 = l_Lean_Elab_Term_elabParen___closed__7;
lean_inc(x_1112);
x_1114 = l_Lean_Syntax_isOfKind(x_1112, x_1113);
if (x_1114 == 0)
{
lean_object* x_1115; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1021);
lean_inc(x_2);
x_1115 = l___private_Lean_Elab_Match_20__collect___main(x_1109, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
if (lean_obj_tag(x_1115) == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
x_1118 = l_Lean_Syntax_setArg(x_1105, x_1108, x_1116);
x_1119 = l_Lean_Syntax_getArg(x_1112, x_1004);
x_1120 = l_Lean_Syntax_getArgs(x_1119);
lean_dec(x_1119);
x_1121 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_1122 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1120, x_1121, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1117);
lean_dec(x_1120);
if (lean_obj_tag(x_1122) == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 x_1125 = x_1122;
} else {
 lean_dec_ref(x_1122);
 x_1125 = lean_box(0);
}
x_1126 = l_Lean_nullKind;
if (lean_is_scalar(x_1107)) {
 x_1127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1127 = x_1107;
}
lean_ctor_set(x_1127, 0, x_1126);
lean_ctor_set(x_1127, 1, x_1123);
x_1128 = l_Lean_Syntax_setArg(x_1112, x_1004, x_1127);
x_1129 = l_Lean_Syntax_setArg(x_1110, x_1108, x_1128);
x_1130 = l_Lean_Syntax_setArg(x_1118, x_1004, x_1129);
x_1131 = lean_array_set(x_11, x_1004, x_1130);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_10);
lean_ctor_set(x_1132, 1, x_1131);
if (lean_is_scalar(x_1125)) {
 x_1133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1133 = x_1125;
}
lean_ctor_set(x_1133, 0, x_1132);
lean_ctor_set(x_1133, 1, x_1124);
return x_1133;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
lean_dec(x_1118);
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_1107);
lean_dec(x_11);
lean_dec(x_10);
x_1134 = lean_ctor_get(x_1122, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1122, 1);
lean_inc(x_1135);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 x_1136 = x_1122;
} else {
 lean_dec_ref(x_1122);
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
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_1107);
lean_dec(x_1105);
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1138 = lean_ctor_get(x_1115, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1115, 1);
lean_inc(x_1139);
if (lean_is_exclusive(x_1115)) {
 lean_ctor_release(x_1115, 0);
 lean_ctor_release(x_1115, 1);
 x_1140 = x_1115;
} else {
 lean_dec_ref(x_1115);
 x_1140 = lean_box(0);
}
if (lean_is_scalar(x_1140)) {
 x_1141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1141 = x_1140;
}
lean_ctor_set(x_1141, 0, x_1138);
lean_ctor_set(x_1141, 1, x_1139);
return x_1141;
}
}
else
{
lean_object* x_1142; 
lean_dec(x_1112);
lean_dec(x_1110);
x_1142 = l___private_Lean_Elab_Match_20__collect___main(x_1109, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1142, 1);
lean_inc(x_1144);
if (lean_is_exclusive(x_1142)) {
 lean_ctor_release(x_1142, 0);
 lean_ctor_release(x_1142, 1);
 x_1145 = x_1142;
} else {
 lean_dec_ref(x_1142);
 x_1145 = lean_box(0);
}
x_1146 = l_Lean_Syntax_setArg(x_1105, x_1108, x_1143);
x_1147 = lean_array_set(x_11, x_1004, x_1146);
if (lean_is_scalar(x_1107)) {
 x_1148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1148 = x_1107;
}
lean_ctor_set(x_1148, 0, x_10);
lean_ctor_set(x_1148, 1, x_1147);
if (lean_is_scalar(x_1145)) {
 x_1149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1149 = x_1145;
}
lean_ctor_set(x_1149, 0, x_1148);
lean_ctor_set(x_1149, 1, x_1144);
return x_1149;
}
else
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
lean_dec(x_1107);
lean_dec(x_1105);
lean_dec(x_11);
lean_dec(x_10);
x_1150 = lean_ctor_get(x_1142, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1142, 1);
lean_inc(x_1151);
if (lean_is_exclusive(x_1142)) {
 lean_ctor_release(x_1142, 0);
 lean_ctor_release(x_1142, 1);
 x_1152 = x_1142;
} else {
 lean_dec_ref(x_1142);
 x_1152 = lean_box(0);
}
if (lean_is_scalar(x_1152)) {
 x_1153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1153 = x_1152;
}
lean_ctor_set(x_1153, 0, x_1150);
lean_ctor_set(x_1153, 1, x_1151);
return x_1153;
}
}
}
else
{
lean_object* x_1154; 
lean_dec(x_1110);
x_1154 = l___private_Lean_Elab_Match_20__collect___main(x_1109, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1154, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1157 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1157 = lean_box(0);
}
x_1158 = l_Lean_Syntax_setArg(x_1105, x_1108, x_1155);
x_1159 = lean_array_set(x_11, x_1004, x_1158);
if (lean_is_scalar(x_1107)) {
 x_1160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1160 = x_1107;
}
lean_ctor_set(x_1160, 0, x_10);
lean_ctor_set(x_1160, 1, x_1159);
if (lean_is_scalar(x_1157)) {
 x_1161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1161 = x_1157;
}
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1156);
return x_1161;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1107);
lean_dec(x_1105);
lean_dec(x_11);
lean_dec(x_10);
x_1162 = lean_ctor_get(x_1154, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1154, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1164 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1164 = lean_box(0);
}
if (lean_is_scalar(x_1164)) {
 x_1165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1165 = x_1164;
}
lean_ctor_set(x_1165, 0, x_1162);
lean_ctor_set(x_1165, 1, x_1163);
return x_1165;
}
}
}
else
{
lean_object* x_1166; 
lean_dec(x_1105);
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1009)) {
 x_1166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1166 = x_1009;
}
lean_ctor_set(x_1166, 0, x_1);
lean_ctor_set(x_1166, 1, x_1008);
return x_1166;
}
}
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
lean_dec(x_1021);
lean_dec(x_1009);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1167 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_1008);
lean_dec(x_8);
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
x_1170 = lean_st_ref_take(x_2, x_1169);
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
lean_dec(x_1170);
x_1173 = lean_ctor_get(x_1171, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1171, 1);
lean_inc(x_1174);
if (lean_is_exclusive(x_1171)) {
 lean_ctor_release(x_1171, 0);
 lean_ctor_release(x_1171, 1);
 x_1175 = x_1171;
} else {
 lean_dec_ref(x_1171);
 x_1175 = lean_box(0);
}
x_1176 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1168);
x_1177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1177, 0, x_1176);
x_1178 = lean_array_push(x_1174, x_1177);
if (lean_is_scalar(x_1175)) {
 x_1179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1179 = x_1175;
}
lean_ctor_set(x_1179, 0, x_1173);
lean_ctor_set(x_1179, 1, x_1178);
x_1180 = lean_st_ref_set(x_2, x_1179, x_1172);
lean_dec(x_2);
x_1181 = lean_ctor_get(x_1180, 1);
lean_inc(x_1181);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 lean_ctor_release(x_1180, 1);
 x_1182 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1182 = lean_box(0);
}
if (lean_is_scalar(x_1182)) {
 x_1183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1183 = x_1182;
}
lean_ctor_set(x_1183, 0, x_1168);
lean_ctor_set(x_1183, 1, x_1181);
return x_1183;
}
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; uint8_t x_1187; 
lean_dec(x_1009);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1184 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1184 = lean_box(0);
}
x_1185 = l_Lean_Syntax_inhabited;
x_1186 = lean_array_get(x_1185, x_11, x_1004);
x_1187 = l_Lean_Syntax_isNone(x_1186);
if (x_1187 == 0)
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
lean_dec(x_1184);
lean_dec(x_11);
lean_dec(x_10);
x_1188 = l___private_Lean_Elab_Match_20__collect___main___closed__17;
x_1189 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_1186, x_1188, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1186);
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1189, 1);
lean_inc(x_1191);
if (lean_is_exclusive(x_1189)) {
 lean_ctor_release(x_1189, 0);
 lean_ctor_release(x_1189, 1);
 x_1192 = x_1189;
} else {
 lean_dec_ref(x_1189);
 x_1192 = lean_box(0);
}
if (lean_is_scalar(x_1192)) {
 x_1193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1193 = x_1192;
}
lean_ctor_set(x_1193, 0, x_1190);
lean_ctor_set(x_1193, 1, x_1191);
return x_1193;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_1186);
x_1194 = lean_unsigned_to_nat(2u);
x_1195 = lean_array_get(x_1185, x_11, x_1194);
x_1196 = l_Lean_Syntax_getArgs(x_1195);
lean_dec(x_1195);
x_1197 = l___private_Lean_Elab_Match_20__collect___main___closed__18;
x_1198 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1196, x_1197, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
lean_dec(x_1196);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 lean_ctor_release(x_1198, 1);
 x_1201 = x_1198;
} else {
 lean_dec_ref(x_1198);
 x_1201 = lean_box(0);
}
x_1202 = l_Lean_nullKind;
if (lean_is_scalar(x_1184)) {
 x_1203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1203 = x_1184;
}
lean_ctor_set(x_1203, 0, x_1202);
lean_ctor_set(x_1203, 1, x_1199);
x_1204 = lean_array_set(x_11, x_1194, x_1203);
x_1205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1205, 0, x_10);
lean_ctor_set(x_1205, 1, x_1204);
if (lean_is_scalar(x_1201)) {
 x_1206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1206 = x_1201;
}
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_1200);
return x_1206;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
lean_dec(x_1184);
lean_dec(x_11);
lean_dec(x_10);
x_1207 = lean_ctor_get(x_1198, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1198, 1);
lean_inc(x_1208);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 lean_ctor_release(x_1198, 1);
 x_1209 = x_1198;
} else {
 lean_dec_ref(x_1198);
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
}
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1009);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1211 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1211 = lean_box(0);
}
x_1212 = l_Lean_Syntax_inhabited;
x_1213 = lean_array_get(x_1212, x_11, x_1004);
x_1214 = l_Lean_Syntax_getArgs(x_1213);
lean_dec(x_1213);
x_1215 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_1216 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1214, x_1215, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
lean_dec(x_1214);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1217 = lean_ctor_get(x_1216, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1216, 1);
lean_inc(x_1218);
if (lean_is_exclusive(x_1216)) {
 lean_ctor_release(x_1216, 0);
 lean_ctor_release(x_1216, 1);
 x_1219 = x_1216;
} else {
 lean_dec_ref(x_1216);
 x_1219 = lean_box(0);
}
x_1220 = l_Lean_nullKind;
if (lean_is_scalar(x_1211)) {
 x_1221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1221 = x_1211;
}
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1217);
x_1222 = lean_array_set(x_11, x_1004, x_1221);
x_1223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1223, 0, x_10);
lean_ctor_set(x_1223, 1, x_1222);
if (lean_is_scalar(x_1219)) {
 x_1224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1224 = x_1219;
}
lean_ctor_set(x_1224, 0, x_1223);
lean_ctor_set(x_1224, 1, x_1218);
return x_1224;
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1211);
lean_dec(x_11);
lean_dec(x_10);
x_1225 = lean_ctor_get(x_1216, 0);
lean_inc(x_1225);
x_1226 = lean_ctor_get(x_1216, 1);
lean_inc(x_1226);
if (lean_is_exclusive(x_1216)) {
 lean_ctor_release(x_1216, 0);
 lean_ctor_release(x_1216, 1);
 x_1227 = x_1216;
} else {
 lean_dec_ref(x_1216);
 x_1227 = lean_box(0);
}
if (lean_is_scalar(x_1227)) {
 x_1228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1228 = x_1227;
}
lean_ctor_set(x_1228, 0, x_1225);
lean_ctor_set(x_1228, 1, x_1226);
return x_1228;
}
}
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
lean_dec(x_1009);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1229 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1229 = lean_box(0);
}
x_1230 = l_Lean_Syntax_inhabited;
x_1231 = lean_unsigned_to_nat(0u);
x_1232 = lean_array_get(x_1230, x_11, x_1231);
x_1233 = lean_array_get(x_1230, x_11, x_1004);
x_1234 = l_Lean_Syntax_getArgs(x_1233);
lean_dec(x_1233);
x_1235 = l_Lean_mkAppStx___closed__6;
lean_inc(x_1021);
x_1236 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_1235, x_1234, x_1231, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1008);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; uint8_t x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1236, 1);
lean_inc(x_1237);
lean_dec(x_1236);
x_1238 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1021);
x_1239 = l___private_Lean_Elab_Match_16__processIdAux(x_1232, x_1238, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1237);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1240 = lean_ctor_get(x_1239, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1239, 1);
lean_inc(x_1241);
lean_dec(x_1239);
x_1242 = x_1234;
x_1243 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed), 11, 3);
lean_closure_set(x_1243, 0, x_1240);
lean_closure_set(x_1243, 1, x_1231);
lean_closure_set(x_1243, 2, x_1242);
x_1244 = x_1243;
x_1245 = lean_apply_8(x_1244, x_2, x_1021, x_4, x_5, x_6, x_7, x_8, x_1241);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1245, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1248 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1248 = lean_box(0);
}
x_1249 = l_Lean_nullKind;
if (lean_is_scalar(x_1229)) {
 x_1250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1250 = x_1229;
}
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1246);
x_1251 = lean_array_set(x_11, x_1004, x_1250);
x_1252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1252, 0, x_10);
lean_ctor_set(x_1252, 1, x_1251);
if (lean_is_scalar(x_1248)) {
 x_1253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1253 = x_1248;
}
lean_ctor_set(x_1253, 0, x_1252);
lean_ctor_set(x_1253, 1, x_1247);
return x_1253;
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1229);
lean_dec(x_11);
lean_dec(x_10);
x_1254 = lean_ctor_get(x_1245, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1245, 1);
lean_inc(x_1255);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1256 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1256 = lean_box(0);
}
if (lean_is_scalar(x_1256)) {
 x_1257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1257 = x_1256;
}
lean_ctor_set(x_1257, 0, x_1254);
lean_ctor_set(x_1257, 1, x_1255);
return x_1257;
}
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
lean_dec(x_1234);
lean_dec(x_1229);
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1258 = lean_ctor_get(x_1239, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1239, 1);
lean_inc(x_1259);
if (lean_is_exclusive(x_1239)) {
 lean_ctor_release(x_1239, 0);
 lean_ctor_release(x_1239, 1);
 x_1260 = x_1239;
} else {
 lean_dec_ref(x_1239);
 x_1260 = lean_box(0);
}
if (lean_is_scalar(x_1260)) {
 x_1261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1261 = x_1260;
}
lean_ctor_set(x_1261, 0, x_1258);
lean_ctor_set(x_1261, 1, x_1259);
return x_1261;
}
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
lean_dec(x_1234);
lean_dec(x_1232);
lean_dec(x_1229);
lean_dec(x_1021);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1262 = lean_ctor_get(x_1236, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1236, 1);
lean_inc(x_1263);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1264 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1264 = lean_box(0);
}
if (lean_is_scalar(x_1264)) {
 x_1265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1265 = x_1264;
}
lean_ctor_set(x_1265, 0, x_1262);
lean_ctor_set(x_1265, 1, x_1263);
return x_1265;
}
}
}
}
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1273 = lean_ctor_get(x_7, 0);
x_1274 = lean_ctor_get(x_7, 1);
x_1275 = lean_ctor_get(x_7, 2);
x_1276 = lean_ctor_get(x_7, 3);
lean_inc(x_1276);
lean_inc(x_1275);
lean_inc(x_1274);
lean_inc(x_1273);
lean_dec(x_7);
x_1277 = l_Lean_replaceRef(x_1, x_1276);
x_1278 = l_Lean_replaceRef(x_1277, x_1276);
lean_dec(x_1277);
x_1279 = l_Lean_replaceRef(x_1278, x_1276);
lean_dec(x_1276);
lean_dec(x_1278);
x_1280 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1280, 0, x_1273);
lean_ctor_set(x_1280, 1, x_1274);
lean_ctor_set(x_1280, 2, x_1275);
lean_ctor_set(x_1280, 3, x_1279);
x_1281 = lean_st_ref_take(x_4, x_9);
if (x_13 == 0)
{
lean_object* x_1556; lean_object* x_1557; uint8_t x_1558; 
x_1556 = lean_ctor_get(x_1281, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1281, 1);
lean_inc(x_1557);
lean_dec(x_1281);
x_1558 = 0;
x_1282 = x_1558;
x_1283 = x_1556;
x_1284 = x_1557;
goto block_1555;
}
else
{
lean_object* x_1559; lean_object* x_1560; uint8_t x_1561; 
x_1559 = lean_ctor_get(x_1281, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1281, 1);
lean_inc(x_1560);
lean_dec(x_1281);
x_1561 = 1;
x_1282 = x_1561;
x_1283 = x_1559;
x_1284 = x_1560;
goto block_1555;
}
block_1555:
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; uint8_t x_1306; uint8_t x_1307; uint8_t x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1285 = lean_ctor_get(x_1283, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1283, 1);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1283, 2);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1283, 3);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1283, 4);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1283, 5);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1283, 6);
lean_inc(x_1291);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 lean_ctor_release(x_1283, 1);
 lean_ctor_release(x_1283, 2);
 lean_ctor_release(x_1283, 3);
 lean_ctor_release(x_1283, 4);
 lean_ctor_release(x_1283, 5);
 lean_ctor_release(x_1283, 6);
 x_1292 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1292 = lean_box(0);
}
x_1293 = lean_unsigned_to_nat(1u);
x_1294 = lean_nat_add(x_1290, x_1293);
if (lean_is_scalar(x_1292)) {
 x_1295 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1295 = x_1292;
}
lean_ctor_set(x_1295, 0, x_1285);
lean_ctor_set(x_1295, 1, x_1286);
lean_ctor_set(x_1295, 2, x_1287);
lean_ctor_set(x_1295, 3, x_1288);
lean_ctor_set(x_1295, 4, x_1289);
lean_ctor_set(x_1295, 5, x_1294);
lean_ctor_set(x_1295, 6, x_1291);
x_1296 = lean_st_ref_set(x_4, x_1295, x_1284);
x_1297 = lean_ctor_get(x_1296, 1);
lean_inc(x_1297);
if (lean_is_exclusive(x_1296)) {
 lean_ctor_release(x_1296, 0);
 lean_ctor_release(x_1296, 1);
 x_1298 = x_1296;
} else {
 lean_dec_ref(x_1296);
 x_1298 = lean_box(0);
}
x_1299 = lean_ctor_get(x_3, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_3, 1);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_3, 2);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_3, 3);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_3, 4);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_3, 5);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_3, 6);
lean_inc(x_1305);
x_1306 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_1307 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_1308 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_1309 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1309 = lean_box(0);
}
if (lean_is_scalar(x_1309)) {
 x_1310 = lean_alloc_ctor(0, 8, 3);
} else {
 x_1310 = x_1309;
}
lean_ctor_set(x_1310, 0, x_1299);
lean_ctor_set(x_1310, 1, x_1300);
lean_ctor_set(x_1310, 2, x_1301);
lean_ctor_set(x_1310, 3, x_1302);
lean_ctor_set(x_1310, 4, x_1303);
lean_ctor_set(x_1310, 5, x_1304);
lean_ctor_set(x_1310, 6, x_1305);
lean_ctor_set(x_1310, 7, x_1290);
lean_ctor_set_uint8(x_1310, sizeof(void*)*8, x_1306);
lean_ctor_set_uint8(x_1310, sizeof(void*)*8 + 1, x_1307);
lean_ctor_set_uint8(x_1310, sizeof(void*)*8 + 2, x_1308);
if (x_1282 == 0)
{
lean_object* x_1311; uint8_t x_1312; 
x_1311 = l___private_Lean_Elab_Match_20__collect___main___closed__2;
x_1312 = lean_name_eq(x_10, x_1311);
if (x_1312 == 0)
{
lean_object* x_1313; uint8_t x_1314; 
x_1313 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_1314 = lean_name_eq(x_10, x_1313);
if (x_1314 == 0)
{
lean_object* x_1315; uint8_t x_1316; 
x_1315 = l_Lean_mkHole___closed__2;
x_1316 = lean_name_eq(x_10, x_1315);
if (x_1316 == 0)
{
lean_object* x_1317; uint8_t x_1318; 
x_1317 = l___private_Lean_Elab_Term_5__hasCDot___main___closed__1;
x_1318 = lean_name_eq(x_10, x_1317);
if (x_1318 == 0)
{
lean_object* x_1319; uint8_t x_1320; 
lean_dec(x_11);
x_1319 = l___private_Lean_Elab_Match_20__collect___main___closed__4;
x_1320 = lean_name_eq(x_10, x_1319);
if (x_1320 == 0)
{
lean_object* x_1321; uint8_t x_1322; 
x_1321 = l___private_Lean_Elab_Match_20__collect___main___closed__5;
x_1322 = lean_name_eq(x_10, x_1321);
if (x_1322 == 0)
{
lean_object* x_1323; uint8_t x_1324; 
x_1323 = l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__2;
x_1324 = lean_name_eq(x_10, x_1323);
if (x_1324 == 0)
{
lean_object* x_1325; uint8_t x_1326; 
x_1325 = l_Lean_strLitKind;
x_1326 = lean_name_eq(x_10, x_1325);
if (x_1326 == 0)
{
lean_object* x_1327; uint8_t x_1328; 
x_1327 = l_Lean_numLitKind;
x_1328 = lean_name_eq(x_10, x_1327);
if (x_1328 == 0)
{
lean_object* x_1329; uint8_t x_1330; 
x_1329 = l_Lean_charLitKind;
x_1330 = lean_name_eq(x_10, x_1329);
if (x_1330 == 0)
{
lean_object* x_1331; uint8_t x_1332; 
lean_dec(x_1298);
lean_dec(x_1);
x_1331 = l_Lean_choiceKind;
x_1332 = lean_name_eq(x_10, x_1331);
lean_dec(x_10);
if (x_1332 == 0)
{
lean_object* x_1333; 
x_1333 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
lean_dec(x_8);
lean_dec(x_1280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1333;
}
else
{
lean_object* x_1334; lean_object* x_1335; 
x_1334 = l___private_Lean_Elab_Match_20__collect___main___closed__8;
x_1335 = l_Lean_throwError___at___private_Lean_Elab_Match_12__throwCtorExpected___spec__1___rarg(x_1334, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
lean_dec(x_8);
lean_dec(x_1280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1335;
}
}
else
{
lean_object* x_1336; 
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1298)) {
 x_1336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1336 = x_1298;
}
lean_ctor_set(x_1336, 0, x_1);
lean_ctor_set(x_1336, 1, x_1297);
return x_1336;
}
}
else
{
lean_object* x_1337; 
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1298)) {
 x_1337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1337 = x_1298;
}
lean_ctor_set(x_1337, 0, x_1);
lean_ctor_set(x_1337, 1, x_1297);
return x_1337;
}
}
else
{
lean_object* x_1338; 
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1298)) {
 x_1338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1338 = x_1298;
}
lean_ctor_set(x_1338, 0, x_1);
lean_ctor_set(x_1338, 1, x_1297);
return x_1338;
}
}
else
{
lean_object* x_1339; 
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1298)) {
 x_1339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1339 = x_1298;
}
lean_ctor_set(x_1339, 0, x_1);
lean_ctor_set(x_1339, 1, x_1297);
return x_1339;
}
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; uint8_t x_1343; lean_object* x_1344; 
lean_dec(x_1298);
lean_dec(x_10);
x_1340 = lean_unsigned_to_nat(0u);
x_1341 = l_Lean_Syntax_getArg(x_1, x_1340);
x_1342 = l_Lean_Syntax_getId(x_1341);
x_1343 = 0;
lean_inc(x_1310);
x_1344 = l___private_Lean_Elab_Match_15__processVar(x_1342, x_1343, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; 
x_1345 = lean_ctor_get(x_1344, 1);
lean_inc(x_1345);
lean_dec(x_1344);
x_1346 = lean_unsigned_to_nat(2u);
x_1347 = l_Lean_Syntax_getArg(x_1, x_1346);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1348 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1348 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_1280);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1310);
x_1349 = l___private_Lean_Elab_Match_20__collect___main(x_1347, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1345);
if (lean_obj_tag(x_1349) == 0)
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec(x_1349);
x_1352 = l_Lean_Elab_Term_getCurrMacroScope(x_1310, x_4, x_5, x_6, x_1280, x_8, x_1351);
lean_dec(x_1280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1310);
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
lean_dec(x_1352);
x_1355 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1354);
lean_dec(x_8);
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
x_1357 = lean_ctor_get(x_1355, 1);
lean_inc(x_1357);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1358 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1358 = lean_box(0);
}
x_1359 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
x_1360 = l_Lean_addMacroScope(x_1356, x_1359, x_1353);
x_1361 = l_Lean_SourceInfo_inhabited___closed__1;
x_1362 = l___private_Lean_Elab_Match_20__collect___main___closed__10;
x_1363 = l___private_Lean_Elab_Match_20__collect___main___closed__13;
x_1364 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1364, 0, x_1361);
lean_ctor_set(x_1364, 1, x_1362);
lean_ctor_set(x_1364, 2, x_1360);
lean_ctor_set(x_1364, 3, x_1363);
x_1365 = l_Array_empty___closed__1;
x_1366 = lean_array_push(x_1365, x_1364);
x_1367 = lean_array_push(x_1365, x_1341);
x_1368 = lean_array_push(x_1367, x_1350);
x_1369 = l_Lean_nullKind___closed__2;
if (lean_is_scalar(x_1348)) {
 x_1370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1370 = x_1348;
}
lean_ctor_set(x_1370, 0, x_1369);
lean_ctor_set(x_1370, 1, x_1368);
x_1371 = lean_array_push(x_1366, x_1370);
x_1372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1372, 0, x_12);
lean_ctor_set(x_1372, 1, x_1371);
if (lean_is_scalar(x_1358)) {
 x_1373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1373 = x_1358;
}
lean_ctor_set(x_1373, 0, x_1372);
lean_ctor_set(x_1373, 1, x_1357);
return x_1373;
}
else
{
lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_dec(x_1348);
lean_dec(x_1341);
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1374 = lean_ctor_get(x_1349, 0);
lean_inc(x_1374);
x_1375 = lean_ctor_get(x_1349, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1349)) {
 lean_ctor_release(x_1349, 0);
 lean_ctor_release(x_1349, 1);
 x_1376 = x_1349;
} else {
 lean_dec_ref(x_1349);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1374);
lean_ctor_set(x_1377, 1, x_1375);
return x_1377;
}
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1341);
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1378 = lean_ctor_get(x_1344, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1344, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1344)) {
 lean_ctor_release(x_1344, 0);
 lean_ctor_release(x_1344, 1);
 x_1380 = x_1344;
} else {
 lean_dec_ref(x_1344);
 x_1380 = lean_box(0);
}
if (lean_is_scalar(x_1380)) {
 x_1381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1381 = x_1380;
}
lean_ctor_set(x_1381, 0, x_1378);
lean_ctor_set(x_1381, 1, x_1379);
return x_1381;
}
}
}
else
{
lean_object* x_1382; lean_object* x_1383; uint8_t x_1384; lean_object* x_1385; 
lean_dec(x_1298);
lean_dec(x_10);
x_1382 = lean_unsigned_to_nat(0u);
x_1383 = l_Lean_Syntax_getArg(x_1, x_1382);
x_1384 = 1;
x_1385 = l___private_Lean_Elab_Match_16__processIdAux(x_1383, x_1384, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
lean_dec(x_2);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1386 = lean_ctor_get(x_1385, 1);
lean_inc(x_1386);
if (lean_is_exclusive(x_1385)) {
 lean_ctor_release(x_1385, 0);
 lean_ctor_release(x_1385, 1);
 x_1387 = x_1385;
} else {
 lean_dec_ref(x_1385);
 x_1387 = lean_box(0);
}
if (lean_is_scalar(x_1387)) {
 x_1388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1388 = x_1387;
}
lean_ctor_set(x_1388, 0, x_1);
lean_ctor_set(x_1388, 1, x_1386);
return x_1388;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_1);
x_1389 = lean_ctor_get(x_1385, 0);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1385, 1);
lean_inc(x_1390);
if (lean_is_exclusive(x_1385)) {
 lean_ctor_release(x_1385, 0);
 lean_ctor_release(x_1385, 1);
 x_1391 = x_1385;
} else {
 lean_dec_ref(x_1385);
 x_1391 = lean_box(0);
}
if (lean_is_scalar(x_1391)) {
 x_1392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1392 = x_1391;
}
lean_ctor_set(x_1392, 0, x_1389);
lean_ctor_set(x_1392, 1, x_1390);
return x_1392;
}
}
}
else
{
lean_object* x_1393; lean_object* x_1394; uint8_t x_1395; 
x_1393 = l_Lean_Syntax_inhabited;
x_1394 = lean_array_get(x_1393, x_11, x_1293);
x_1395 = l_Lean_Syntax_isNone(x_1394);
if (x_1395 == 0)
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; uint8_t x_1400; 
lean_dec(x_1298);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1396 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1396 = lean_box(0);
}
x_1397 = lean_unsigned_to_nat(0u);
x_1398 = l_Lean_Syntax_getArg(x_1394, x_1397);
x_1399 = l_Lean_Syntax_getArg(x_1394, x_1293);
x_1400 = l_Lean_Syntax_isNone(x_1399);
if (x_1400 == 0)
{
lean_object* x_1401; lean_object* x_1402; uint8_t x_1403; 
x_1401 = l_Lean_Syntax_getArg(x_1399, x_1397);
x_1402 = l_Lean_Elab_Term_elabParen___closed__7;
lean_inc(x_1401);
x_1403 = l_Lean_Syntax_isOfKind(x_1401, x_1402);
if (x_1403 == 0)
{
lean_object* x_1404; 
lean_inc(x_8);
lean_inc(x_1280);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1310);
lean_inc(x_2);
x_1404 = l___private_Lean_Elab_Match_20__collect___main(x_1398, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
if (lean_obj_tag(x_1404) == 0)
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
x_1405 = lean_ctor_get(x_1404, 0);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1404, 1);
lean_inc(x_1406);
lean_dec(x_1404);
x_1407 = l_Lean_Syntax_setArg(x_1394, x_1397, x_1405);
x_1408 = l_Lean_Syntax_getArg(x_1401, x_1293);
x_1409 = l_Lean_Syntax_getArgs(x_1408);
lean_dec(x_1408);
x_1410 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_1411 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1409, x_1410, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1406);
lean_dec(x_1409);
if (lean_obj_tag(x_1411) == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1412 = lean_ctor_get(x_1411, 0);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_1411, 1);
lean_inc(x_1413);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 lean_ctor_release(x_1411, 1);
 x_1414 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1414 = lean_box(0);
}
x_1415 = l_Lean_nullKind;
if (lean_is_scalar(x_1396)) {
 x_1416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1416 = x_1396;
}
lean_ctor_set(x_1416, 0, x_1415);
lean_ctor_set(x_1416, 1, x_1412);
x_1417 = l_Lean_Syntax_setArg(x_1401, x_1293, x_1416);
x_1418 = l_Lean_Syntax_setArg(x_1399, x_1397, x_1417);
x_1419 = l_Lean_Syntax_setArg(x_1407, x_1293, x_1418);
x_1420 = lean_array_set(x_11, x_1293, x_1419);
x_1421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1421, 0, x_10);
lean_ctor_set(x_1421, 1, x_1420);
if (lean_is_scalar(x_1414)) {
 x_1422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1422 = x_1414;
}
lean_ctor_set(x_1422, 0, x_1421);
lean_ctor_set(x_1422, 1, x_1413);
return x_1422;
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
lean_dec(x_1407);
lean_dec(x_1401);
lean_dec(x_1399);
lean_dec(x_1396);
lean_dec(x_11);
lean_dec(x_10);
x_1423 = lean_ctor_get(x_1411, 0);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1411, 1);
lean_inc(x_1424);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 lean_ctor_release(x_1411, 1);
 x_1425 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1425 = lean_box(0);
}
if (lean_is_scalar(x_1425)) {
 x_1426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1426 = x_1425;
}
lean_ctor_set(x_1426, 0, x_1423);
lean_ctor_set(x_1426, 1, x_1424);
return x_1426;
}
}
else
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
lean_dec(x_1401);
lean_dec(x_1399);
lean_dec(x_1396);
lean_dec(x_1394);
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1427 = lean_ctor_get(x_1404, 0);
lean_inc(x_1427);
x_1428 = lean_ctor_get(x_1404, 1);
lean_inc(x_1428);
if (lean_is_exclusive(x_1404)) {
 lean_ctor_release(x_1404, 0);
 lean_ctor_release(x_1404, 1);
 x_1429 = x_1404;
} else {
 lean_dec_ref(x_1404);
 x_1429 = lean_box(0);
}
if (lean_is_scalar(x_1429)) {
 x_1430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1430 = x_1429;
}
lean_ctor_set(x_1430, 0, x_1427);
lean_ctor_set(x_1430, 1, x_1428);
return x_1430;
}
}
else
{
lean_object* x_1431; 
lean_dec(x_1401);
lean_dec(x_1399);
x_1431 = l___private_Lean_Elab_Match_20__collect___main(x_1398, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
if (lean_obj_tag(x_1431) == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
x_1432 = lean_ctor_get(x_1431, 0);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1431, 1);
lean_inc(x_1433);
if (lean_is_exclusive(x_1431)) {
 lean_ctor_release(x_1431, 0);
 lean_ctor_release(x_1431, 1);
 x_1434 = x_1431;
} else {
 lean_dec_ref(x_1431);
 x_1434 = lean_box(0);
}
x_1435 = l_Lean_Syntax_setArg(x_1394, x_1397, x_1432);
x_1436 = lean_array_set(x_11, x_1293, x_1435);
if (lean_is_scalar(x_1396)) {
 x_1437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1437 = x_1396;
}
lean_ctor_set(x_1437, 0, x_10);
lean_ctor_set(x_1437, 1, x_1436);
if (lean_is_scalar(x_1434)) {
 x_1438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1438 = x_1434;
}
lean_ctor_set(x_1438, 0, x_1437);
lean_ctor_set(x_1438, 1, x_1433);
return x_1438;
}
else
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
lean_dec(x_1396);
lean_dec(x_1394);
lean_dec(x_11);
lean_dec(x_10);
x_1439 = lean_ctor_get(x_1431, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1431, 1);
lean_inc(x_1440);
if (lean_is_exclusive(x_1431)) {
 lean_ctor_release(x_1431, 0);
 lean_ctor_release(x_1431, 1);
 x_1441 = x_1431;
} else {
 lean_dec_ref(x_1431);
 x_1441 = lean_box(0);
}
if (lean_is_scalar(x_1441)) {
 x_1442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1442 = x_1441;
}
lean_ctor_set(x_1442, 0, x_1439);
lean_ctor_set(x_1442, 1, x_1440);
return x_1442;
}
}
}
else
{
lean_object* x_1443; 
lean_dec(x_1399);
x_1443 = l___private_Lean_Elab_Match_20__collect___main(x_1398, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
if (lean_obj_tag(x_1443) == 0)
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
x_1444 = lean_ctor_get(x_1443, 0);
lean_inc(x_1444);
x_1445 = lean_ctor_get(x_1443, 1);
lean_inc(x_1445);
if (lean_is_exclusive(x_1443)) {
 lean_ctor_release(x_1443, 0);
 lean_ctor_release(x_1443, 1);
 x_1446 = x_1443;
} else {
 lean_dec_ref(x_1443);
 x_1446 = lean_box(0);
}
x_1447 = l_Lean_Syntax_setArg(x_1394, x_1397, x_1444);
x_1448 = lean_array_set(x_11, x_1293, x_1447);
if (lean_is_scalar(x_1396)) {
 x_1449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1449 = x_1396;
}
lean_ctor_set(x_1449, 0, x_10);
lean_ctor_set(x_1449, 1, x_1448);
if (lean_is_scalar(x_1446)) {
 x_1450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1450 = x_1446;
}
lean_ctor_set(x_1450, 0, x_1449);
lean_ctor_set(x_1450, 1, x_1445);
return x_1450;
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
lean_dec(x_1396);
lean_dec(x_1394);
lean_dec(x_11);
lean_dec(x_10);
x_1451 = lean_ctor_get(x_1443, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1443, 1);
lean_inc(x_1452);
if (lean_is_exclusive(x_1443)) {
 lean_ctor_release(x_1443, 0);
 lean_ctor_release(x_1443, 1);
 x_1453 = x_1443;
} else {
 lean_dec_ref(x_1443);
 x_1453 = lean_box(0);
}
if (lean_is_scalar(x_1453)) {
 x_1454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1454 = x_1453;
}
lean_ctor_set(x_1454, 0, x_1451);
lean_ctor_set(x_1454, 1, x_1452);
return x_1454;
}
}
}
else
{
lean_object* x_1455; 
lean_dec(x_1394);
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_1298)) {
 x_1455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1455 = x_1298;
}
lean_ctor_set(x_1455, 0, x_1);
lean_ctor_set(x_1455, 1, x_1297);
return x_1455;
}
}
}
else
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
lean_dec(x_1310);
lean_dec(x_1298);
lean_dec(x_1280);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1456 = l___private_Lean_Elab_Match_10__mkMVarSyntax___rarg(x_8, x_1297);
lean_dec(x_8);
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1456, 1);
lean_inc(x_1458);
lean_dec(x_1456);
x_1459 = lean_st_ref_take(x_2, x_1458);
x_1460 = lean_ctor_get(x_1459, 0);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1459, 1);
lean_inc(x_1461);
lean_dec(x_1459);
x_1462 = lean_ctor_get(x_1460, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1460, 1);
lean_inc(x_1463);
if (lean_is_exclusive(x_1460)) {
 lean_ctor_release(x_1460, 0);
 lean_ctor_release(x_1460, 1);
 x_1464 = x_1460;
} else {
 lean_dec_ref(x_1460);
 x_1464 = lean_box(0);
}
x_1465 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1457);
x_1466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1466, 0, x_1465);
x_1467 = lean_array_push(x_1463, x_1466);
if (lean_is_scalar(x_1464)) {
 x_1468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1468 = x_1464;
}
lean_ctor_set(x_1468, 0, x_1462);
lean_ctor_set(x_1468, 1, x_1467);
x_1469 = lean_st_ref_set(x_2, x_1468, x_1461);
lean_dec(x_2);
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
 x_1472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1472 = x_1471;
}
lean_ctor_set(x_1472, 0, x_1457);
lean_ctor_set(x_1472, 1, x_1470);
return x_1472;
}
}
else
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; uint8_t x_1476; 
lean_dec(x_1298);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1473 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1473 = lean_box(0);
}
x_1474 = l_Lean_Syntax_inhabited;
x_1475 = lean_array_get(x_1474, x_11, x_1293);
x_1476 = l_Lean_Syntax_isNone(x_1475);
if (x_1476 == 0)
{
lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
lean_dec(x_1473);
lean_dec(x_11);
lean_dec(x_10);
x_1477 = l___private_Lean_Elab_Match_20__collect___main___closed__17;
x_1478 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_1475, x_1477, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
lean_dec(x_8);
lean_dec(x_1280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1475);
x_1479 = lean_ctor_get(x_1478, 0);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1478, 1);
lean_inc(x_1480);
if (lean_is_exclusive(x_1478)) {
 lean_ctor_release(x_1478, 0);
 lean_ctor_release(x_1478, 1);
 x_1481 = x_1478;
} else {
 lean_dec_ref(x_1478);
 x_1481 = lean_box(0);
}
if (lean_is_scalar(x_1481)) {
 x_1482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1482 = x_1481;
}
lean_ctor_set(x_1482, 0, x_1479);
lean_ctor_set(x_1482, 1, x_1480);
return x_1482;
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
lean_dec(x_1475);
x_1483 = lean_unsigned_to_nat(2u);
x_1484 = lean_array_get(x_1474, x_11, x_1483);
x_1485 = l_Lean_Syntax_getArgs(x_1484);
lean_dec(x_1484);
x_1486 = l___private_Lean_Elab_Match_20__collect___main___closed__18;
x_1487 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1485, x_1486, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
lean_dec(x_1485);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1487, 1);
lean_inc(x_1489);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1490 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1490 = lean_box(0);
}
x_1491 = l_Lean_nullKind;
if (lean_is_scalar(x_1473)) {
 x_1492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1492 = x_1473;
}
lean_ctor_set(x_1492, 0, x_1491);
lean_ctor_set(x_1492, 1, x_1488);
x_1493 = lean_array_set(x_11, x_1483, x_1492);
x_1494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1494, 0, x_10);
lean_ctor_set(x_1494, 1, x_1493);
if (lean_is_scalar(x_1490)) {
 x_1495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1495 = x_1490;
}
lean_ctor_set(x_1495, 0, x_1494);
lean_ctor_set(x_1495, 1, x_1489);
return x_1495;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
lean_dec(x_1473);
lean_dec(x_11);
lean_dec(x_10);
x_1496 = lean_ctor_get(x_1487, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1487, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1498 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1498 = lean_box(0);
}
if (lean_is_scalar(x_1498)) {
 x_1499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1499 = x_1498;
}
lean_ctor_set(x_1499, 0, x_1496);
lean_ctor_set(x_1499, 1, x_1497);
return x_1499;
}
}
}
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
lean_dec(x_1298);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1500 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1500 = lean_box(0);
}
x_1501 = l_Lean_Syntax_inhabited;
x_1502 = lean_array_get(x_1501, x_11, x_1293);
x_1503 = l_Lean_Syntax_getArgs(x_1502);
lean_dec(x_1502);
x_1504 = l___private_Lean_Elab_Match_20__collect___main___closed__14;
x_1505 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1503, x_1504, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
lean_dec(x_1503);
if (lean_obj_tag(x_1505) == 0)
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1506 = lean_ctor_get(x_1505, 0);
lean_inc(x_1506);
x_1507 = lean_ctor_get(x_1505, 1);
lean_inc(x_1507);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1508 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1508 = lean_box(0);
}
x_1509 = l_Lean_nullKind;
if (lean_is_scalar(x_1500)) {
 x_1510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1510 = x_1500;
}
lean_ctor_set(x_1510, 0, x_1509);
lean_ctor_set(x_1510, 1, x_1506);
x_1511 = lean_array_set(x_11, x_1293, x_1510);
x_1512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1512, 0, x_10);
lean_ctor_set(x_1512, 1, x_1511);
if (lean_is_scalar(x_1508)) {
 x_1513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1513 = x_1508;
}
lean_ctor_set(x_1513, 0, x_1512);
lean_ctor_set(x_1513, 1, x_1507);
return x_1513;
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; 
lean_dec(x_1500);
lean_dec(x_11);
lean_dec(x_10);
x_1514 = lean_ctor_get(x_1505, 0);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1505, 1);
lean_inc(x_1515);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1516 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1516 = lean_box(0);
}
if (lean_is_scalar(x_1516)) {
 x_1517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1517 = x_1516;
}
lean_ctor_set(x_1517, 0, x_1514);
lean_ctor_set(x_1517, 1, x_1515);
return x_1517;
}
}
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
lean_dec(x_1298);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1518 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1518 = lean_box(0);
}
x_1519 = l_Lean_Syntax_inhabited;
x_1520 = lean_unsigned_to_nat(0u);
x_1521 = lean_array_get(x_1519, x_11, x_1520);
x_1522 = lean_array_get(x_1519, x_11, x_1293);
x_1523 = l_Lean_Syntax_getArgs(x_1522);
lean_dec(x_1522);
x_1524 = l_Lean_mkAppStx___closed__6;
lean_inc(x_1310);
x_1525 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_1524, x_1523, x_1520, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1297);
if (lean_obj_tag(x_1525) == 0)
{
lean_object* x_1526; uint8_t x_1527; lean_object* x_1528; 
x_1526 = lean_ctor_get(x_1525, 1);
lean_inc(x_1526);
lean_dec(x_1525);
x_1527 = 1;
lean_inc(x_8);
lean_inc(x_1280);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1310);
x_1528 = l___private_Lean_Elab_Match_16__processIdAux(x_1521, x_1527, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1526);
if (lean_obj_tag(x_1528) == 0)
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1529 = lean_ctor_get(x_1528, 0);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_1528, 1);
lean_inc(x_1530);
lean_dec(x_1528);
x_1531 = x_1523;
x_1532 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed), 11, 3);
lean_closure_set(x_1532, 0, x_1529);
lean_closure_set(x_1532, 1, x_1520);
lean_closure_set(x_1532, 2, x_1531);
x_1533 = x_1532;
x_1534 = lean_apply_8(x_1533, x_2, x_1310, x_4, x_5, x_6, x_1280, x_8, x_1530);
if (lean_obj_tag(x_1534) == 0)
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1535 = lean_ctor_get(x_1534, 0);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1534, 1);
lean_inc(x_1536);
if (lean_is_exclusive(x_1534)) {
 lean_ctor_release(x_1534, 0);
 lean_ctor_release(x_1534, 1);
 x_1537 = x_1534;
} else {
 lean_dec_ref(x_1534);
 x_1537 = lean_box(0);
}
x_1538 = l_Lean_nullKind;
if (lean_is_scalar(x_1518)) {
 x_1539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1539 = x_1518;
}
lean_ctor_set(x_1539, 0, x_1538);
lean_ctor_set(x_1539, 1, x_1535);
x_1540 = lean_array_set(x_11, x_1293, x_1539);
x_1541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1541, 0, x_10);
lean_ctor_set(x_1541, 1, x_1540);
if (lean_is_scalar(x_1537)) {
 x_1542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1542 = x_1537;
}
lean_ctor_set(x_1542, 0, x_1541);
lean_ctor_set(x_1542, 1, x_1536);
return x_1542;
}
else
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_1518);
lean_dec(x_11);
lean_dec(x_10);
x_1543 = lean_ctor_get(x_1534, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1534, 1);
lean_inc(x_1544);
if (lean_is_exclusive(x_1534)) {
 lean_ctor_release(x_1534, 0);
 lean_ctor_release(x_1534, 1);
 x_1545 = x_1534;
} else {
 lean_dec_ref(x_1534);
 x_1545 = lean_box(0);
}
if (lean_is_scalar(x_1545)) {
 x_1546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1546 = x_1545;
}
lean_ctor_set(x_1546, 0, x_1543);
lean_ctor_set(x_1546, 1, x_1544);
return x_1546;
}
}
else
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_1523);
lean_dec(x_1518);
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1547 = lean_ctor_get(x_1528, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1528, 1);
lean_inc(x_1548);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 lean_ctor_release(x_1528, 1);
 x_1549 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1549 = lean_box(0);
}
if (lean_is_scalar(x_1549)) {
 x_1550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1550 = x_1549;
}
lean_ctor_set(x_1550, 0, x_1547);
lean_ctor_set(x_1550, 1, x_1548);
return x_1550;
}
}
else
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
lean_dec(x_1523);
lean_dec(x_1521);
lean_dec(x_1518);
lean_dec(x_1310);
lean_dec(x_1280);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1551 = lean_ctor_get(x_1525, 0);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1525, 1);
lean_inc(x_1552);
if (lean_is_exclusive(x_1525)) {
 lean_ctor_release(x_1525, 0);
 lean_ctor_release(x_1525, 1);
 x_1553 = x_1525;
} else {
 lean_dec_ref(x_1525);
 x_1553 = lean_box(0);
}
if (lean_is_scalar(x_1553)) {
 x_1554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1554 = x_1553;
}
lean_ctor_set(x_1554, 0, x_1551);
lean_ctor_set(x_1554, 1, x_1552);
return x_1554;
}
}
}
}
}
case 3:
{
lean_object* x_1562; 
lean_inc(x_1);
x_1562 = l___private_Lean_Elab_Match_18__processId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_1562) == 0)
{
uint8_t x_1563; 
x_1563 = !lean_is_exclusive(x_1562);
if (x_1563 == 0)
{
lean_object* x_1564; 
x_1564 = lean_ctor_get(x_1562, 0);
lean_dec(x_1564);
lean_ctor_set(x_1562, 0, x_1);
return x_1562;
}
else
{
lean_object* x_1565; lean_object* x_1566; 
x_1565 = lean_ctor_get(x_1562, 1);
lean_inc(x_1565);
lean_dec(x_1562);
x_1566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1566, 0, x_1);
lean_ctor_set(x_1566, 1, x_1565);
return x_1566;
}
}
else
{
uint8_t x_1567; 
lean_dec(x_1);
x_1567 = !lean_is_exclusive(x_1562);
if (x_1567 == 0)
{
return x_1562;
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1568 = lean_ctor_get(x_1562, 0);
x_1569 = lean_ctor_get(x_1562, 1);
lean_inc(x_1569);
lean_inc(x_1568);
lean_dec(x_1562);
x_1570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1570, 0, x_1568);
lean_ctor_set(x_1570, 1, x_1569);
return x_1570;
}
}
}
default: 
{
lean_object* x_1571; 
lean_dec(x_1);
x_1571 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1571;
}
}
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___private_Lean_Elab_Match_20__collect___main___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_20__collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_20__collect___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
x_43 = lean_ctor_get(x_26, 5);
x_44 = lean_ctor_get(x_26, 6);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_45 = l_Std_PersistentArray_push___rarg(x_40, x_24);
x_46 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_42);
lean_ctor_set(x_46, 5, x_43);
lean_ctor_set(x_46, 6, x_44);
x_47 = lean_st_ref_set(x_6, x_46, x_27);
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
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
lean_dec(x_14);
x_53 = lean_ctor_get(x_5, 0);
x_54 = lean_ctor_get(x_5, 1);
x_55 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_FileMap_toPosition(x_54, x_52);
x_59 = lean_box(0);
x_60 = l_String_splitAux___main___closed__1;
lean_inc(x_53);
x_61 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*5, x_3);
x_62 = lean_st_ref_take(x_6, x_57);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_63, 2);
x_67 = l_Std_PersistentArray_push___rarg(x_66, x_61);
lean_ctor_set(x_63, 2, x_67);
x_68 = lean_st_ref_set(x_6, x_63, x_64);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
x_77 = lean_ctor_get(x_63, 2);
x_78 = lean_ctor_get(x_63, 3);
x_79 = lean_ctor_get(x_63, 4);
x_80 = lean_ctor_get(x_63, 5);
x_81 = lean_ctor_get(x_63, 6);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
x_82 = l_Std_PersistentArray_push___rarg(x_77, x_61);
x_83 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_79);
lean_ctor_set(x_83, 5, x_80);
lean_ctor_set(x_83, 6, x_81);
x_84 = lean_st_ref_set(x_6, x_83, x_64);
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
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
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
x_20 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
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
x_22 = l___private_Lean_Elab_Match_20__collect___main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_39 = l___private_Lean_Elab_Match_20__collect___main(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
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
lean_object* _init_l___private_Lean_Elab_Match_21__collectPatternVars___closed__1() {
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
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l___private_Lean_Elab_Match_21__collectPatternVars___closed__1;
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
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_24 = l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(x_15, x_21, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
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
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = l_Lean_Expr_fvarId_x21(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_array_push(x_2, x_16);
x_18 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_3, x_4, x_14, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_19 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_4, x_5, x_15, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__2(x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_2);
x_30 = 0;
x_31 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabImplicitLambda___main___spec__1___rarg(x_23, x_30, x_27, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
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
x_38 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
lean_inc(x_3);
x_39 = l_Lean_Name_appendIndexAfter(x_38, x_3);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed), 13, 5);
lean_closure_set(x_40, 0, x_3);
lean_closure_set(x_40, 1, x_32);
lean_closure_set(x_40, 2, x_4);
lean_closure_set(x_40, 3, x_1);
lean_closure_set(x_40, 4, x_2);
x_41 = 0;
x_42 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabImplicitLambda___main___spec__1___rarg(x_39, x_41, x_36, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_mkFreshExprMVarWithId___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_23__withPatternVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_23__withPatternVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_23__withPatternVars___rarg), 9, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected match type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Elab_Term_elabTermEnsuringType(x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_28 = lean_expr_instantiate1(x_20, x_24);
lean_dec(x_20);
x_29 = lean_array_push(x_4, x_24);
x_2 = x_27;
x_3 = x_28;
x_4 = x_29;
x_11 = x_25;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3;
x_37 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_4);
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
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_24__elabPatternsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_24__elabPatternsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_24__elabPatternsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_20 = l_Lean_mkMVar(x_18);
lean_inc(x_5);
lean_inc(x_20);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_68 = lean_ctor_get(x_9, 0);
x_69 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_70 = l_Lean_checkTraceOption(x_68, x_69);
if (x_70 == 0)
{
lean_dec(x_20);
x_24 = x_23;
goto block_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_20);
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
x_30 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_31 = l_Lean_checkTraceOption(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_7);
lean_inc(x_5);
x_32 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
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
x_54 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
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
x_86 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_85, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_25__alreadyVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Match_26__markAsVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_Match_26__markAsVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_26__markAsVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Lean_indentExpr(x_10);
x_12 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = (uint8_t)((x_6 << 24) >> 61);
x_12 = lean_box(x_11);
x_13 = lean_array_push(x_4, x_12);
x_2 = x_10;
x_3 = x_5;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_5;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg___boxed), 2, 0);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
x_40 = lean_ctor_get(x_24, 2);
x_41 = lean_ctor_get(x_24, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_42 = l_Lean_MetavarContext_assignExpr(x_38, x_1, x_2);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_st_ref_set(x_7, x_43, x_25);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = l_Lean_TraceState_Inhabited___closed__1;
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_17);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_take(x_7, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 3);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
x_65 = l_Lean_MetavarContext_assignExpr(x_60, x_1, x_2);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 4, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_63);
x_67 = lean_st_ref_set(x_7, x_66, x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
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
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_29__mkLocalDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Expr_mvarId_x21(x_1);
x_11 = lean_st_ref_get(x_2, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_10);
x_14 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg(x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_Meta_inferType___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
x_23 = l_Lean_mkFVar(x_18);
x_24 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__4(x_10, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Meta_Closure_mkNextUserName___rarg___closed__2;
x_31 = l_Lean_Name_appendIndexAfter(x_30, x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = 0;
lean_inc(x_18);
x_34 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_21);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_33);
x_35 = lean_st_ref_take(x_2, x_25);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
x_41 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5(x_1, x_39, x_32);
lean_dec(x_1);
x_42 = lean_box(0);
lean_inc(x_18);
x_43 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_18, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_array_push(x_39, x_34);
lean_ctor_set(x_36, 2, x_43);
lean_ctor_set(x_36, 1, x_44);
x_45 = lean_st_ref_set(x_2, x_36, x_37);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_18);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = l_Array_insertAt___rarg(x_39, x_52, x_34);
lean_dec(x_52);
lean_ctor_set(x_36, 2, x_43);
lean_ctor_set(x_36, 1, x_53);
x_54 = lean_st_ref_set(x_2, x_36, x_37);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_18);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_36, 0);
x_62 = lean_ctor_get(x_36, 1);
x_63 = lean_ctor_get(x_36, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_36);
x_64 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5(x_1, x_62, x_32);
lean_dec(x_1);
x_65 = lean_box(0);
lean_inc(x_18);
x_66 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_63, x_18, x_65);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_array_push(x_62, x_34);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_66);
x_69 = lean_st_ref_set(x_2, x_68, x_37);
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
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_18);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = l_Array_insertAt___rarg(x_62, x_74, x_34);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_61);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_66);
x_77 = lean_st_ref_set(x_2, x_76, x_37);
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
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_18);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
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
uint8_t x_86; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_14);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_14, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_15, 0);
lean_inc(x_88);
lean_dec(x_15);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_14, 0, x_89);
return x_14;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_14, 1);
lean_inc(x_90);
lean_dec(x_14);
x_91 = lean_ctor_get(x_15, 0);
lean_inc(x_91);
lean_dec(x_15);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
}
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_29__mkLocalDeclFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_29__mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_30__getFieldsBinderInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(x_1, x_4, x_3, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_30__getFieldsBinderInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_30__getFieldsBinderInfo(x_1);
lean_dec(x_1);
return x_2;
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
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
lean_dec(x_4);
lean_dec(x_2);
x_14 = x_3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_16 = lean_array_fget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fset(x_3, x_2, x_17);
x_27 = x_16;
x_28 = l_Lean_BinderInfo_inhabited;
x_29 = lean_box(x_28);
x_30 = lean_array_get(x_29, x_1, x_2);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = l_Lean_BinderInfo_isExplicit(x_31);
if (x_32 == 0)
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_st_ref_get(x_4, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_array_get_size(x_37);
x_39 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(x_33, x_35, x_37, x_38, x_17);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_27);
x_19 = x_40;
x_20 = x_36;
goto block_26;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l___private_Lean_Elab_Match_25__alreadyVisited(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_Elab_Match_26__markAsVisited(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Expr_fvarId_x21(x_27);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_19 = x_48;
x_20 = x_46;
goto block_26;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_27);
x_19 = x_50;
x_20 = x_49;
goto block_26;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_27);
x_19 = x_51;
x_20 = x_11;
goto block_26;
}
}
else
{
lean_object* x_52; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_19 = x_53;
x_20 = x_54;
goto block_26;
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_18, x_2, x_23);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_24;
x_11 = x_20;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
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
lean_dec(x_4);
lean_dec(x_2);
x_14 = x_3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_16 = lean_array_fget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fset(x_3, x_2, x_17);
x_27 = x_16;
x_28 = l_Lean_BinderInfo_inhabited;
x_29 = lean_box(x_28);
x_30 = lean_array_get(x_29, x_1, x_2);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = l_Lean_BinderInfo_isExplicit(x_31);
if (x_32 == 0)
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_st_ref_get(x_4, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_array_get_size(x_37);
x_39 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_33, x_35, x_37, x_38, x_17);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_27);
x_19 = x_40;
x_20 = x_36;
goto block_26;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l___private_Lean_Elab_Match_25__alreadyVisited(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_Elab_Match_26__markAsVisited(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Expr_fvarId_x21(x_27);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_19 = x_48;
x_20 = x_46;
goto block_26;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_27);
x_19 = x_50;
x_20 = x_49;
goto block_26;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_27);
x_19 = x_51;
x_20 = x_11;
goto block_26;
}
}
else
{
lean_object* x_52; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_19 = x_53;
x_20 = x_54;
goto block_26;
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_18, x_2, x_23);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_24;
x_11 = x_20;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_37 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l___private_Lean_Elab_Match_20__collect___main___closed__11;
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
x_33 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
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
x_48 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_53 = l_Array_extract___rarg(x_42, x_36, x_44);
x_54 = l_Array_extract___rarg(x_42, x_44, x_43);
lean_dec(x_43);
lean_dec(x_42);
x_55 = l___private_Lean_Elab_Match_30__getFieldsBinderInfo(x_35);
x_56 = x_54;
x_57 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5___boxed), 11, 3);
lean_closure_set(x_57, 0, x_55);
lean_closure_set(x_57, 1, x_36);
lean_closure_set(x_57, 2, x_56);
x_58 = x_57;
x_59 = lean_apply_8(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_35, 0);
lean_inc(x_60);
lean_dec(x_35);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Array_toList___rarg(x_53);
lean_dec(x_53);
x_65 = l_Array_toList___rarg(x_62);
lean_dec(x_62);
x_66 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_27);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_59, 0, x_66);
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_59, 0);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_59);
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
lean_dec(x_60);
x_70 = l_Array_toList___rarg(x_53);
lean_dec(x_53);
x_71 = l_Array_toList___rarg(x_67);
lean_dec(x_67);
x_72 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set(x_72, 2, x_70);
lean_ctor_set(x_72, 3, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_53);
lean_dec(x_35);
lean_dec(x_27);
x_74 = !lean_is_exclusive(x_59);
if (x_74 == 0)
{
return x_59;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_59, 0);
x_76 = lean_ctor_get(x_59, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_59);
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
lean_object* x_78; 
lean_dec(x_34);
lean_dec(x_27);
x_78 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
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
lean_object* x_79; 
lean_dec(x_25);
x_79 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_20);
if (x_80 == 0)
{
return x_20;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_20, 0);
x_82 = lean_ctor_get(x_20, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_20);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; 
x_84 = l___private_Lean_Elab_Match_29__mkLocalDeclFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_85 = l_Lean_Expr_fvarId_x21(x_1);
x_105 = lean_st_ref_get(x_2, x_9);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
x_109 = lean_array_get_size(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(x_85, x_106, x_108, x_109, x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_106);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
lean_dec(x_85);
x_112 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_107);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
return x_112;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
x_86 = x_107;
goto block_104;
}
block_104:
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l___private_Lean_Elab_Match_25__alreadyVisited(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_1);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_85);
x_91 = l___private_Lean_Elab_Match_26__markAsVisited(x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_85);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_87);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_87, 0);
lean_dec(x_99);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_87, 0, x_100);
return x_87;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_dec(x_87);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_1);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_1);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_9);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_9);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_1);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_9);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_unsigned_to_nat(0u);
x_124 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_123);
x_125 = lean_unsigned_to_nat(2u);
x_126 = lean_nat_sub(x_124, x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_126, x_127);
lean_dec(x_126);
x_129 = l_Lean_Expr_getRevArg_x21___main(x_1, x_128);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_130 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
x_134 = lean_nat_sub(x_124, x_127);
lean_dec(x_124);
x_135 = lean_nat_sub(x_134, x_127);
lean_dec(x_134);
x_136 = l_Lean_Expr_getRevArg_x21___main(x_1, x_135);
lean_dec(x_1);
if (lean_obj_tag(x_136) == 1)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
lean_ctor_set(x_130, 0, x_138);
return x_130;
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_136);
lean_free_object(x_130);
lean_dec(x_132);
x_139 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_140 = l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg(x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_130, 0);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_130);
x_143 = lean_nat_sub(x_124, x_127);
lean_dec(x_124);
x_144 = lean_nat_sub(x_143, x_127);
lean_dec(x_143);
x_145 = l_Lean_Expr_getRevArg_x21___main(x_1, x_144);
lean_dec(x_1);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_145);
lean_dec(x_141);
x_149 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_150 = l_Lean_throwError___at___private_Lean_Elab_Match_27__throwInvalidPattern___spec__1___rarg(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_124);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_130);
if (x_151 == 0)
{
return x_130;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_130, 0);
x_153 = lean_ctor_get(x_130, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_130);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_1);
x_155 = lean_ctor_get(x_11, 0);
lean_inc(x_155);
lean_dec(x_11);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_158, 0, x_161);
return x_158;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_158, 0);
x_163 = lean_ctor_get(x_158, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_158);
x_164 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_164, 0, x_156);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
uint8_t x_166; 
lean_dec(x_156);
x_166 = !lean_is_exclusive(x_158);
if (x_166 == 0)
{
return x_158;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_158, 0);
x_168 = lean_ctor_get(x_158, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_158);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
lean_object* x_170; 
lean_dec(x_1);
x_170 = lean_ctor_get(x_10, 0);
lean_inc(x_170);
lean_dec(x_10);
if (lean_obj_tag(x_170) == 1)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_st_ref_get(x_2, x_9);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
x_177 = lean_array_get_size(x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8(x_171, x_174, x_176, x_177, x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_174);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_172, 0, x_180);
return x_172;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_free_object(x_172);
x_181 = l___private_Lean_Elab_Match_25__alreadyVisited(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_175);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_185 = l___private_Lean_Elab_Match_26__markAsVisited(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_185, 0);
lean_dec(x_187);
x_188 = l_Lean_Expr_fvarId_x21(x_170);
lean_dec(x_170);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_185, 0, x_189);
return x_185;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
lean_dec(x_185);
x_191 = l_Lean_Expr_fvarId_x21(x_170);
lean_dec(x_170);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_181);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_181, 0);
lean_dec(x_195);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_170);
lean_ctor_set(x_181, 0, x_196);
return x_181;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_181, 1);
lean_inc(x_197);
lean_dec(x_181);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_170);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_172, 0);
x_201 = lean_ctor_get(x_172, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_172);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
x_203 = lean_array_get_size(x_202);
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8(x_171, x_200, x_202, x_203, x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_170);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_201);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = l___private_Lean_Elab_Match_25__alreadyVisited(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = l___private_Lean_Elab_Match_26__markAsVisited(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_211);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_215 = l_Lean_Expr_fvarId_x21(x_170);
lean_dec(x_170);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_219 = x_208;
} else {
 lean_dec_ref(x_208);
 x_219 = lean_box(0);
}
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_170);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
return x_221;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_170);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_9);
return x_223;
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
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__8(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Array_toList___rarg(x_3);
x_13 = l_Array_toList___rarg(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_9(x_1, x_14, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_empty___closed__1;
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_24__elabPatternsAux___boxed), 11, 4);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_withSynthesize___rarg(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_inc(x_7);
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_finalizePatternDecls(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = x_18;
x_24 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1___boxed), 9, 2);
lean_closure_set(x_24, 0, x_12);
lean_closure_set(x_24, 1, x_23);
x_25 = x_24;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = lean_apply_7(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1___boxed), 11, 2);
lean_closure_set(x_29, 0, x_4);
lean_closure_set(x_29, 1, x_19);
x_30 = l_Lean_Elab_Term_withDepElimPatterns___rarg(x_21, x_27, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_elabTermEnsuringType(x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = l_List_redLength___main___rarg(x_18);
x_20 = lean_mk_empty_array_with_capacity(x_19);
lean_dec(x_19);
x_21 = l_List_toArrayAux___main___rarg(x_18, x_20);
x_22 = x_21;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_23, x_22);
x_25 = x_24;
x_26 = l_Array_isEmpty___rarg(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_14);
lean_inc(x_7);
lean_inc(x_5);
x_27 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_25, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_inc(x_2);
x_32 = l_Lean_checkTraceOption(x_31, x_2);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_free_object(x_27);
lean_inc(x_29);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_35 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_29);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
x_46 = lean_ctor_get(x_9, 0);
lean_inc(x_46);
lean_inc(x_2);
x_47 = l_Lean_checkTraceOption(x_46, x_2);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_44);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_44);
x_51 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_44);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
return x_27;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_27, 0);
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_27);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_25);
x_62 = l_Lean_mkThunk(x_16);
x_63 = lean_ctor_get(x_9, 0);
lean_inc(x_63);
lean_inc(x_2);
x_64 = l_Lean_checkTraceOption(x_63, x_2);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_14, 0, x_65);
return x_14;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_free_object(x_14);
lean_inc(x_62);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_62);
x_67 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_3);
lean_ctor_set(x_74, 1, x_62);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_76 = lean_ctor_get(x_14, 0);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_14);
x_78 = lean_ctor_get(x_3, 0);
lean_inc(x_78);
x_79 = l_List_redLength___main___rarg(x_78);
x_80 = lean_mk_empty_array_with_capacity(x_79);
lean_dec(x_79);
x_81 = l_List_toArrayAux___main___rarg(x_78, x_80);
x_82 = x_81;
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Array_umapMAux___main___at_Lean_Meta_Closure_mkBinding___spec__1(x_83, x_82);
x_85 = x_84;
x_86 = l_Array_isEmpty___rarg(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_inc(x_7);
lean_inc(x_5);
x_87 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_85, x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_9, 0);
lean_inc(x_91);
lean_inc(x_2);
x_92 = l_Lean_checkTraceOption(x_91, x_2);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_90;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_90);
lean_inc(x_88);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_88);
x_96 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_97, x_5, x_6, x_7, x_8, x_9, x_10, x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_3);
lean_ctor_set(x_101, 1, x_88);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_105 = x_87;
} else {
 lean_dec_ref(x_87);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_85);
x_107 = l_Lean_mkThunk(x_76);
x_108 = lean_ctor_get(x_9, 0);
lean_inc(x_108);
lean_inc(x_2);
x_109 = l_Lean_checkTraceOption(x_108, x_2);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_3);
lean_ctor_set(x_110, 1, x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_77);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_inc(x_107);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_113 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_114 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2, x_114, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_3);
lean_ctor_set(x_118, 1, x_107);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_14);
if (x_120 == 0)
{
return x_14;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_14, 0);
x_122 = lean_ctor_get(x_14, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_14);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__1), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(x_4, x_12, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
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
x_17 = l___private_Lean_Elab_Match_21__collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_22 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_23 = l_Lean_checkTraceOption(x_12, x_22);
lean_dec(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 11, 3);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
x_25 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_20, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
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
x_37 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_20, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
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
x_50 = l___private_Lean_Elab_Match_21__collectPatternVars(x_1, x_3, x_4, x_5, x_6, x_49, x_8, x_9);
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
x_55 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_56 = l_Lean_checkTraceOption(x_42, x_55);
lean_dec(x_42);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 11, 3);
lean_closure_set(x_57, 0, x_54);
lean_closure_set(x_57, 1, x_55);
lean_closure_set(x_57, 2, x_2);
x_58 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_53, x_57, x_3, x_4, x_5, x_6, x_49, x_8, x_52);
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
x_70 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_53, x_69, x_3, x_4, x_5, x_6, x_49, x_8, x_68);
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
x_12 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg(x_1, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Elab_Term_mkElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_Meta_Match_mkElim(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_23);
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
x_45 = l_Lean_Meta_Match_mkElim(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_44);
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
lean_object* l_Lean_Elab_Term_mkElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_mkElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(lean_object* x_1) {
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
x_11 = l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(x_5);
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
x_19 = l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing cases:");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportElimResultErrors___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportElimResultErrors___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_reportElimResultErrors___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unused alternatives: ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportElimResultErrors___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportElimResultErrors___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportElimResultErrors___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_reportElimResultErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_Elab_Term_reportElimResultErrors___closed__4;
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
x_21 = l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(x_19);
x_22 = l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Term_reportElimResultErrors___closed__7;
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
lean_object* l_Lean_Elab_Term_reportElimResultErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_reportElimResultErrors(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabImplicitLambdaAux___spec__1___boxed), 9, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elim");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchType: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_get_size(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l___private_Lean_Elab_Match_5__elabMatchOptType(x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_expandMacrosInPatterns(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_19 = l___private_Lean_Elab_Match_7__elabDiscrs(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_112 = lean_ctor_get(x_9, 0);
lean_inc(x_112);
x_113 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_114 = l_Lean_checkTraceOption(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
x_22 = x_21;
goto block_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_inc(x_14);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_14);
x_116 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__9;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_113, x_117, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_22 = x_119;
goto block_111;
}
block_111:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = x_17;
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__1), 10, 3);
lean_closure_set(x_25, 0, x_14);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_23);
x_26 = x_25;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = lean_apply_7(x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = x_28;
lean_inc(x_30);
x_31 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__2(x_24, x_30);
x_32 = x_31;
x_33 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__3(x_24, x_30);
x_34 = x_33;
x_35 = lean_array_get_size(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_35);
lean_inc(x_14);
x_36 = l_Lean_Elab_Term_mkMotiveType(x_14, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_40 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___rarg(x_14, x_39, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__3;
lean_inc(x_5);
x_45 = l_Lean_Elab_Term_mkAuxName(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Array_toList___rarg(x_34);
lean_dec(x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_49 = l_Lean_Elab_Term_mkElim(x_46, x_37, x_35, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_5);
lean_inc(x_50);
x_52 = l_Lean_Elab_Term_reportElimResultErrors(x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l_Lean_mkApp(x_56, x_42);
x_58 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_20, x_20, x_24, x_57);
lean_dec(x_20);
x_59 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_32, x_32, x_24, x_58);
lean_dec(x_32);
x_60 = lean_ctor_get(x_9, 0);
lean_inc(x_60);
x_61 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_62 = l_Lean_checkTraceOption(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_52, 0, x_59);
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_52);
lean_inc(x_59);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_59);
x_64 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_61, x_65, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_59);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_dec(x_52);
x_72 = lean_ctor_get(x_50, 0);
lean_inc(x_72);
lean_dec(x_50);
x_73 = l_Lean_mkApp(x_72, x_42);
x_74 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_20, x_20, x_24, x_73);
lean_dec(x_20);
x_75 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_32, x_32, x_24, x_74);
lean_dec(x_32);
x_76 = lean_ctor_get(x_9, 0);
lean_inc(x_76);
x_77 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_78 = l_Lean_checkTraceOption(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_71);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_75);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_81 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_77, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_75);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_50);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_52);
if (x_87 == 0)
{
return x_52;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_52, 0);
x_89 = lean_ctor_get(x_52, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_52);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_91 = !lean_is_exclusive(x_49);
if (x_91 == 0)
{
return x_49;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_49, 0);
x_93 = lean_ctor_get(x_49, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_49);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_95 = !lean_is_exclusive(x_45);
if (x_95 == 0)
{
return x_45;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_45, 0);
x_97 = lean_ctor_get(x_45, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_45);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_99 = !lean_is_exclusive(x_41);
if (x_99 == 0)
{
return x_41;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_41, 0);
x_101 = lean_ctor_get(x_41, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_41);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_103 = !lean_is_exclusive(x_36);
if (x_103 == 0)
{
return x_36;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_36, 0);
x_105 = lean_ctor_get(x_36, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_36);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_107 = !lean_is_exclusive(x_27);
if (x_107 == 0)
{
return x_27;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_27, 0);
x_109 = lean_ctor_get(x_27, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_27);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_120 = !lean_is_exclusive(x_19);
if (x_120 == 0)
{
return x_19;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_19, 0);
x_122 = lean_ctor_get(x_19, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_124 = !lean_is_exclusive(x_16);
if (x_124 == 0)
{
return x_16;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_16, 0);
x_126 = lean_ctor_get(x_16, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_16);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_13);
if (x_128 == 0)
{
return x_13;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_13, 0);
x_130 = lean_ctor_get(x_13, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_13);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_32__elabMatchAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Match_33__waitExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Elab_Match_33__waitExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_33__waitExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_34__elabMatchCore___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_Match_33__waitExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_21 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_34__elabMatchCore___spec__1(x_17, x_20);
x_22 = x_21;
x_23 = l___private_Lean_Elab_Match_8__getMatchAlts(x_1);
x_24 = l_Lean_Syntax_getArg(x_1, x_16);
x_25 = l___private_Lean_Elab_Match_32__elabMatchAux(x_22, x_23, x_24, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_24);
lean_dec(x_22);
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
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Match_34__elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_2 = l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("→");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__10;
x_2 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__3;
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
x_20 = l___private_Lean_Elab_Match_35__mkMatchType___main(x_1, x_19, x_3, x_8);
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
x_31 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__2;
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
x_37 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__28;
x_38 = lean_array_push(x_37, x_36);
x_39 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
x_40 = lean_array_push(x_38, x_39);
x_41 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
x_42 = lean_array_push(x_40, x_41);
x_43 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__45;
x_44 = lean_array_push(x_42, x_43);
x_45 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_33, x_46);
x_48 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
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
x_59 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
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
x_64 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
x_65 = lean_array_push(x_64, x_22);
x_66 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
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
x_78 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__2;
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
x_84 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__28;
x_85 = lean_array_push(x_84, x_83);
x_86 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
x_87 = lean_array_push(x_85, x_86);
x_88 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
x_89 = lean_array_push(x_87, x_88);
x_90 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__45;
x_91 = lean_array_push(x_89, x_90);
x_92 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_80, x_93);
x_95 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
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
x_106 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
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
x_112 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
x_113 = lean_array_push(x_112, x_68);
x_114 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
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
x_127 = l___private_Lean_Elab_Match_35__mkMatchType___main(x_1, x_126, x_120, x_8);
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
x_139 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__2;
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
x_145 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__28;
x_146 = lean_array_push(x_145, x_144);
x_147 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
x_148 = lean_array_push(x_146, x_147);
x_149 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__44;
x_150 = lean_array_push(x_148, x_149);
x_151 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__45;
x_152 = lean_array_push(x_150, x_151);
x_153 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_array_push(x_141, x_154);
x_156 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
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
x_167 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
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
x_173 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
x_174 = lean_array_push(x_173, x_128);
x_175 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__7;
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
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_35__mkMatchType___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_35__mkMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_35__mkMatchType___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_35__mkMatchType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_36__mkOptType(lean_object* x_1) {
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
lean_object* _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq.refl");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4() {
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
lean_object* _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_30 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3;
x_31 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5;
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Lean_mkAppStx___closed__8;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__3;
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
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_37__mkNewDiscrs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid number of patterns, expected #");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_15 = l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1;
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
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_38__mkNewPatterns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_38__mkNewPatterns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_38__mkNewPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_39__mkNewAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = l_Array_empty___closed__1;
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Match_38__mkNewPatterns___main(x_2, x_1, x_7, x_5, x_8, x_3, x_4);
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
lean_object* l___private_Lean_Elab_Match_39__mkNewAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_39__mkNewAlt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_40__mkNewAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_39__mkNewAlt___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1(x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_40__mkNewAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_40__mkNewAlts(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match expected type should not be provided when discriminants with equality proofs are used");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1(x_1, x_10, x_11, x_8);
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
x_17 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1;
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
x_20 = l___private_Lean_Elab_Match_35__mkMatchType___main(x_6, x_8, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_copyInfo(x_21, x_1);
x_24 = l___private_Lean_Elab_Match_36__mkOptType(x_23);
x_25 = l_Lean_Syntax_setArg(x_1, x_7, x_24);
lean_inc(x_2);
x_26 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main(x_6, x_8, x_9, x_2, x_22);
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
x_36 = l___private_Lean_Elab_Match_40__mkNewAlts(x_6, x_35, x_2, x_28);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* x_10; lean_object* x_11; uint8_t x_37; lean_object* x_1545; uint8_t x_1546; 
x_1545 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
lean_inc(x_1);
x_1546 = l_Lean_Syntax_isOfKind(x_1, x_1545);
if (x_1546 == 0)
{
uint8_t x_1547; 
x_1547 = 0;
x_37 = x_1547;
goto block_1544;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; uint8_t x_1551; 
x_1548 = l_Lean_Syntax_getArgs(x_1);
x_1549 = lean_array_get_size(x_1548);
lean_dec(x_1548);
x_1550 = lean_unsigned_to_nat(5u);
x_1551 = lean_nat_dec_eq(x_1549, x_1550);
lean_dec(x_1549);
x_37 = x_1551;
goto block_1544;
}
block_36:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_34__elabMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
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
block_1544:
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
x_48 = lean_ctor_get(x_46, 5);
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
x_53 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_52, x_48);
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
x_60 = lean_ctor_get(x_57, 5);
lean_dec(x_60);
lean_ctor_set(x_57, 5, x_55);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
x_65 = lean_ctor_get(x_57, 2);
x_66 = lean_ctor_get(x_57, 3);
x_67 = lean_ctor_get(x_57, 4);
x_68 = lean_ctor_get(x_57, 6);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_55);
lean_ctor_set(x_69, 6, x_68);
x_70 = lean_st_ref_set(x_4, x_69, x_58);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_10 = x_54;
x_11 = x_71;
goto block_36;
}
}
else
{
lean_object* x_72; 
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
lean_dec(x_53);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_73, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_73);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_47);
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
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_1538; uint8_t x_1539; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = l_Lean_Syntax_getArg(x_1, x_87);
x_1538 = l_Lean_nullKind___closed__2;
lean_inc(x_88);
x_1539 = l_Lean_Syntax_isOfKind(x_88, x_1538);
if (x_1539 == 0)
{
uint8_t x_1540; 
x_1540 = 0;
x_89 = x_1540;
goto block_1537;
}
else
{
lean_object* x_1541; lean_object* x_1542; uint8_t x_1543; 
x_1541 = l_Lean_Syntax_getArgs(x_88);
x_1542 = lean_array_get_size(x_1541);
lean_dec(x_1541);
x_1543 = lean_nat_dec_eq(x_1542, x_87);
lean_dec(x_1542);
x_89 = x_1543;
goto block_1537;
}
block_1537:
{
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_88);
x_90 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_get(x_8, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_4, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 5);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_7, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_7, 2);
lean_inc(x_102);
x_103 = lean_environment_main_module(x_96);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_91);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
lean_inc(x_1);
x_105 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_104, x_100);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_4, x_99);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_109, 5);
lean_dec(x_112);
lean_ctor_set(x_109, 5, x_107);
x_113 = lean_st_ref_set(x_4, x_109, x_110);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_10 = x_106;
x_11 = x_114;
goto block_36;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_ctor_get(x_109, 0);
x_116 = lean_ctor_get(x_109, 1);
x_117 = lean_ctor_get(x_109, 2);
x_118 = lean_ctor_get(x_109, 3);
x_119 = lean_ctor_get(x_109, 4);
x_120 = lean_ctor_get(x_109, 6);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_117);
lean_ctor_set(x_121, 3, x_118);
lean_ctor_set(x_121, 4, x_119);
lean_ctor_set(x_121, 5, x_107);
lean_ctor_set(x_121, 6, x_120);
x_122 = lean_st_ref_set(x_4, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_10 = x_106;
x_11 = x_123;
goto block_36;
}
}
else
{
lean_object* x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_ctor_get(x_105, 0);
lean_inc(x_124);
lean_dec(x_105);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_125, x_128, x_3, x_4, x_5, x_6, x_7, x_8, x_99);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_125);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
return x_129;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_129);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
else
{
lean_object* x_134; uint8_t x_135; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_99);
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
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_1530; uint8_t x_1531; 
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lean_Syntax_getArg(x_88, x_139);
lean_dec(x_88);
x_1530 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_inc(x_140);
x_1531 = l_Lean_Syntax_isOfKind(x_140, x_1530);
if (x_1531 == 0)
{
uint8_t x_1532; 
x_1532 = 0;
x_141 = x_1532;
goto block_1529;
}
else
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; 
x_1533 = l_Lean_Syntax_getArgs(x_140);
x_1534 = lean_array_get_size(x_1533);
lean_dec(x_1533);
x_1535 = lean_unsigned_to_nat(2u);
x_1536 = lean_nat_dec_eq(x_1534, x_1535);
lean_dec(x_1534);
x_141 = x_1536;
goto block_1529;
}
block_1529:
{
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_140);
x_142 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_get(x_8, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_st_ref_get(x_4, x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 5);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_7, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_7, 2);
lean_inc(x_154);
x_155 = lean_environment_main_module(x_148);
x_156 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_143);
lean_ctor_set(x_156, 2, x_153);
lean_ctor_set(x_156, 3, x_154);
lean_inc(x_1);
x_157 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_156, x_152);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_st_ref_take(x_4, x_151);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = !lean_is_exclusive(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_161, 5);
lean_dec(x_164);
lean_ctor_set(x_161, 5, x_159);
x_165 = lean_st_ref_set(x_4, x_161, x_162);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_10 = x_158;
x_11 = x_166;
goto block_36;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_167 = lean_ctor_get(x_161, 0);
x_168 = lean_ctor_get(x_161, 1);
x_169 = lean_ctor_get(x_161, 2);
x_170 = lean_ctor_get(x_161, 3);
x_171 = lean_ctor_get(x_161, 4);
x_172 = lean_ctor_get(x_161, 6);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_161);
x_173 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_168);
lean_ctor_set(x_173, 2, x_169);
lean_ctor_set(x_173, 3, x_170);
lean_ctor_set(x_173, 4, x_171);
lean_ctor_set(x_173, 5, x_159);
lean_ctor_set(x_173, 6, x_172);
x_174 = lean_st_ref_set(x_4, x_173, x_162);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_10 = x_158;
x_11 = x_175;
goto block_36;
}
}
else
{
lean_object* x_176; 
lean_dec(x_2);
lean_dec(x_1);
x_176 = lean_ctor_get(x_157, 0);
lean_inc(x_176);
lean_dec(x_157);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_177, x_180, x_3, x_4, x_5, x_6, x_7, x_8, x_151);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_177);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
return x_181;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_181);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_186 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_151);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
return x_186;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_186);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
else
{
lean_object* x_191; uint8_t x_192; lean_object* x_1523; uint8_t x_1524; 
x_191 = l_Lean_Syntax_getArg(x_140, x_139);
x_1523 = l_Lean_nullKind___closed__2;
lean_inc(x_191);
x_1524 = l_Lean_Syntax_isOfKind(x_191, x_1523);
if (x_1524 == 0)
{
uint8_t x_1525; 
lean_dec(x_191);
x_1525 = 0;
x_192 = x_1525;
goto block_1522;
}
else
{
lean_object* x_1526; lean_object* x_1527; uint8_t x_1528; 
x_1526 = l_Lean_Syntax_getArgs(x_191);
lean_dec(x_191);
x_1527 = lean_array_get_size(x_1526);
lean_dec(x_1526);
x_1528 = lean_nat_dec_eq(x_1527, x_139);
lean_dec(x_1527);
x_192 = x_1528;
goto block_1522;
}
block_1522:
{
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_140);
x_193 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_st_ref_get(x_8, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_st_ref_get(x_4, x_198);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_ctor_get(x_201, 5);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_7, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_7, 2);
lean_inc(x_205);
x_206 = lean_environment_main_module(x_199);
x_207 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_194);
lean_ctor_set(x_207, 2, x_204);
lean_ctor_set(x_207, 3, x_205);
lean_inc(x_1);
x_208 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_207, x_203);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_st_ref_take(x_4, x_202);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_212, 5);
lean_dec(x_215);
lean_ctor_set(x_212, 5, x_210);
x_216 = lean_st_ref_set(x_4, x_212, x_213);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_10 = x_209;
x_11 = x_217;
goto block_36;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_218 = lean_ctor_get(x_212, 0);
x_219 = lean_ctor_get(x_212, 1);
x_220 = lean_ctor_get(x_212, 2);
x_221 = lean_ctor_get(x_212, 3);
x_222 = lean_ctor_get(x_212, 4);
x_223 = lean_ctor_get(x_212, 6);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_212);
x_224 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_224, 0, x_218);
lean_ctor_set(x_224, 1, x_219);
lean_ctor_set(x_224, 2, x_220);
lean_ctor_set(x_224, 3, x_221);
lean_ctor_set(x_224, 4, x_222);
lean_ctor_set(x_224, 5, x_210);
lean_ctor_set(x_224, 6, x_223);
x_225 = lean_st_ref_set(x_4, x_224, x_213);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_10 = x_209;
x_11 = x_226;
goto block_36;
}
}
else
{
lean_object* x_227; 
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_208, 0);
lean_inc(x_227);
lean_dec(x_208);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_228, x_231, x_3, x_4, x_5, x_6, x_7, x_8, x_202);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_228);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
return x_232;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_232, 0);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_232);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
else
{
lean_object* x_237; uint8_t x_238; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_237 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_202);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
return x_237;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_237);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_934; uint8_t x_935; uint8_t x_936; 
x_242 = l_Lean_Syntax_getArg(x_140, x_87);
lean_dec(x_140);
x_243 = lean_unsigned_to_nat(2u);
x_244 = l_Lean_Syntax_getArg(x_1, x_243);
x_934 = l_Lean_nullKind___closed__2;
lean_inc(x_244);
x_935 = l_Lean_Syntax_isOfKind(x_244, x_934);
if (x_935 == 0)
{
uint8_t x_1518; 
x_1518 = 0;
x_936 = x_1518;
goto block_1517;
}
else
{
lean_object* x_1519; lean_object* x_1520; uint8_t x_1521; 
x_1519 = l_Lean_Syntax_getArgs(x_244);
x_1520 = lean_array_get_size(x_1519);
lean_dec(x_1519);
x_1521 = lean_nat_dec_eq(x_1520, x_139);
lean_dec(x_1520);
x_936 = x_1521;
goto block_1517;
}
block_933:
{
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_244);
lean_dec(x_242);
x_246 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_st_ref_get(x_8, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_st_ref_get(x_4, x_251);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 5);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_7, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_7, 2);
lean_inc(x_258);
x_259 = lean_environment_main_module(x_252);
x_260 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_247);
lean_ctor_set(x_260, 2, x_257);
lean_ctor_set(x_260, 3, x_258);
lean_inc(x_1);
x_261 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_260, x_256);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_st_ref_take(x_4, x_255);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = !lean_is_exclusive(x_265);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_265, 5);
lean_dec(x_268);
lean_ctor_set(x_265, 5, x_263);
x_269 = lean_st_ref_set(x_4, x_265, x_266);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_10 = x_262;
x_11 = x_270;
goto block_36;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_271 = lean_ctor_get(x_265, 0);
x_272 = lean_ctor_get(x_265, 1);
x_273 = lean_ctor_get(x_265, 2);
x_274 = lean_ctor_get(x_265, 3);
x_275 = lean_ctor_get(x_265, 4);
x_276 = lean_ctor_get(x_265, 6);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_265);
x_277 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_277, 0, x_271);
lean_ctor_set(x_277, 1, x_272);
lean_ctor_set(x_277, 2, x_273);
lean_ctor_set(x_277, 3, x_274);
lean_ctor_set(x_277, 4, x_275);
lean_ctor_set(x_277, 5, x_263);
lean_ctor_set(x_277, 6, x_276);
x_278 = lean_st_ref_set(x_4, x_277, x_266);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_10 = x_262;
x_11 = x_279;
goto block_36;
}
}
else
{
lean_object* x_280; 
lean_dec(x_2);
lean_dec(x_1);
x_280 = lean_ctor_get(x_261, 0);
lean_inc(x_280);
lean_dec(x_261);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_283, 0, x_282);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_283);
x_285 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_281, x_284, x_3, x_4, x_5, x_6, x_7, x_8, x_255);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_281);
x_286 = !lean_is_exclusive(x_285);
if (x_286 == 0)
{
return x_285;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_285, 0);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_285);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
else
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_290 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_255);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
return x_290;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_290, 0);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_290);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
}
else
{
lean_object* x_295; uint8_t x_296; lean_object* x_927; uint8_t x_928; 
x_295 = l_Lean_Syntax_getArg(x_244, x_139);
lean_dec(x_244);
x_927 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_inc(x_295);
x_928 = l_Lean_Syntax_isOfKind(x_295, x_927);
if (x_928 == 0)
{
uint8_t x_929; 
x_929 = 0;
x_296 = x_929;
goto block_926;
}
else
{
lean_object* x_930; lean_object* x_931; uint8_t x_932; 
x_930 = l_Lean_Syntax_getArgs(x_295);
x_931 = lean_array_get_size(x_930);
lean_dec(x_930);
x_932 = lean_nat_dec_eq(x_931, x_243);
lean_dec(x_931);
x_296 = x_932;
goto block_926;
}
block_926:
{
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_295);
lean_dec(x_242);
x_297 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_st_ref_get(x_8, x_299);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_st_ref_get(x_4, x_302);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_305, 5);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_ctor_get(x_7, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_7, 2);
lean_inc(x_309);
x_310 = lean_environment_main_module(x_303);
x_311 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_298);
lean_ctor_set(x_311, 2, x_308);
lean_ctor_set(x_311, 3, x_309);
lean_inc(x_1);
x_312 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_311, x_307);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_st_ref_take(x_4, x_306);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = !lean_is_exclusive(x_316);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_316, 5);
lean_dec(x_319);
lean_ctor_set(x_316, 5, x_314);
x_320 = lean_st_ref_set(x_4, x_316, x_317);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_10 = x_313;
x_11 = x_321;
goto block_36;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_316, 0);
x_323 = lean_ctor_get(x_316, 1);
x_324 = lean_ctor_get(x_316, 2);
x_325 = lean_ctor_get(x_316, 3);
x_326 = lean_ctor_get(x_316, 4);
x_327 = lean_ctor_get(x_316, 6);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_316);
x_328 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_328, 0, x_322);
lean_ctor_set(x_328, 1, x_323);
lean_ctor_set(x_328, 2, x_324);
lean_ctor_set(x_328, 3, x_325);
lean_ctor_set(x_328, 4, x_326);
lean_ctor_set(x_328, 5, x_314);
lean_ctor_set(x_328, 6, x_327);
x_329 = lean_st_ref_set(x_4, x_328, x_317);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_10 = x_313;
x_11 = x_330;
goto block_36;
}
}
else
{
lean_object* x_331; 
lean_dec(x_2);
lean_dec(x_1);
x_331 = lean_ctor_get(x_312, 0);
lean_inc(x_331);
lean_dec(x_312);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_335 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_335, 0, x_334);
x_336 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_332, x_335, x_3, x_4, x_5, x_6, x_7, x_8, x_306);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_332);
x_337 = !lean_is_exclusive(x_336);
if (x_337 == 0)
{
return x_336;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_336, 0);
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_336);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
else
{
lean_object* x_341; uint8_t x_342; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_341 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_306);
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
return x_341;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_341, 0);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_341);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_920; uint8_t x_921; 
x_346 = l_Lean_Syntax_getArg(x_295, x_87);
lean_dec(x_295);
x_347 = lean_unsigned_to_nat(4u);
x_348 = l_Lean_Syntax_getArg(x_1, x_347);
x_920 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
lean_inc(x_348);
x_921 = l_Lean_Syntax_isOfKind(x_348, x_920);
if (x_921 == 0)
{
uint8_t x_922; 
x_922 = 0;
x_349 = x_922;
goto block_919;
}
else
{
lean_object* x_923; lean_object* x_924; uint8_t x_925; 
x_923 = l_Lean_Syntax_getArgs(x_348);
x_924 = lean_array_get_size(x_923);
lean_dec(x_923);
x_925 = lean_nat_dec_eq(x_924, x_243);
lean_dec(x_924);
x_349 = x_925;
goto block_919;
}
block_919:
{
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_242);
x_350 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_st_ref_get(x_8, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
lean_dec(x_354);
x_357 = lean_st_ref_get(x_4, x_355);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_ctor_get(x_358, 5);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_ctor_get(x_7, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_7, 2);
lean_inc(x_362);
x_363 = lean_environment_main_module(x_356);
x_364 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_351);
lean_ctor_set(x_364, 2, x_361);
lean_ctor_set(x_364, 3, x_362);
lean_inc(x_1);
x_365 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_364, x_360);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_st_ref_take(x_4, x_359);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = !lean_is_exclusive(x_369);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_369, 5);
lean_dec(x_372);
lean_ctor_set(x_369, 5, x_367);
x_373 = lean_st_ref_set(x_4, x_369, x_370);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
lean_dec(x_373);
x_10 = x_366;
x_11 = x_374;
goto block_36;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_375 = lean_ctor_get(x_369, 0);
x_376 = lean_ctor_get(x_369, 1);
x_377 = lean_ctor_get(x_369, 2);
x_378 = lean_ctor_get(x_369, 3);
x_379 = lean_ctor_get(x_369, 4);
x_380 = lean_ctor_get(x_369, 6);
lean_inc(x_380);
lean_inc(x_379);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_369);
x_381 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_381, 0, x_375);
lean_ctor_set(x_381, 1, x_376);
lean_ctor_set(x_381, 2, x_377);
lean_ctor_set(x_381, 3, x_378);
lean_ctor_set(x_381, 4, x_379);
lean_ctor_set(x_381, 5, x_367);
lean_ctor_set(x_381, 6, x_380);
x_382 = lean_st_ref_set(x_4, x_381, x_370);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_10 = x_366;
x_11 = x_383;
goto block_36;
}
}
else
{
lean_object* x_384; 
lean_dec(x_2);
lean_dec(x_1);
x_384 = lean_ctor_get(x_365, 0);
lean_inc(x_384);
lean_dec(x_365);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_387, 0, x_386);
x_388 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_388, 0, x_387);
x_389 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_385, x_388, x_3, x_4, x_5, x_6, x_7, x_8, x_359);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_385);
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
return x_389;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_389, 0);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_389);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
else
{
lean_object* x_394; uint8_t x_395; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_394 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_359);
x_395 = !lean_is_exclusive(x_394);
if (x_395 == 0)
{
return x_394;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_394, 0);
x_397 = lean_ctor_get(x_394, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_394);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
}
else
{
lean_object* x_399; uint8_t x_400; lean_object* x_680; uint8_t x_681; uint8_t x_682; 
x_399 = l_Lean_Syntax_getArg(x_348, x_139);
x_680 = l_Lean_nullKind___closed__2;
lean_inc(x_399);
x_681 = l_Lean_Syntax_isOfKind(x_399, x_680);
if (x_681 == 0)
{
uint8_t x_915; 
x_915 = 0;
x_682 = x_915;
goto block_914;
}
else
{
lean_object* x_916; lean_object* x_917; uint8_t x_918; 
x_916 = l_Lean_Syntax_getArgs(x_399);
x_917 = lean_array_get_size(x_916);
lean_dec(x_916);
x_918 = lean_nat_dec_eq(x_917, x_139);
lean_dec(x_917);
x_682 = x_918;
goto block_914;
}
block_679:
{
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_242);
x_401 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_st_ref_get(x_8, x_403);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_st_ref_get(x_4, x_406);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get(x_409, 5);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_ctor_get(x_7, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_7, 2);
lean_inc(x_413);
x_414 = lean_environment_main_module(x_407);
x_415 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_402);
lean_ctor_set(x_415, 2, x_412);
lean_ctor_set(x_415, 3, x_413);
lean_inc(x_1);
x_416 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_415, x_411);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_st_ref_take(x_4, x_410);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = !lean_is_exclusive(x_420);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_420, 5);
lean_dec(x_423);
lean_ctor_set(x_420, 5, x_418);
x_424 = lean_st_ref_set(x_4, x_420, x_421);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec(x_424);
x_10 = x_417;
x_11 = x_425;
goto block_36;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_426 = lean_ctor_get(x_420, 0);
x_427 = lean_ctor_get(x_420, 1);
x_428 = lean_ctor_get(x_420, 2);
x_429 = lean_ctor_get(x_420, 3);
x_430 = lean_ctor_get(x_420, 4);
x_431 = lean_ctor_get(x_420, 6);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_420);
x_432 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_432, 0, x_426);
lean_ctor_set(x_432, 1, x_427);
lean_ctor_set(x_432, 2, x_428);
lean_ctor_set(x_432, 3, x_429);
lean_ctor_set(x_432, 4, x_430);
lean_ctor_set(x_432, 5, x_418);
lean_ctor_set(x_432, 6, x_431);
x_433 = lean_st_ref_set(x_4, x_432, x_421);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec(x_433);
x_10 = x_417;
x_11 = x_434;
goto block_36;
}
}
else
{
lean_object* x_435; 
lean_dec(x_2);
lean_dec(x_1);
x_435 = lean_ctor_get(x_416, 0);
lean_inc(x_435);
lean_dec(x_416);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_438, 0, x_437);
x_439 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_439, 0, x_438);
x_440 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_436, x_439, x_3, x_4, x_5, x_6, x_7, x_8, x_410);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_436);
x_441 = !lean_is_exclusive(x_440);
if (x_441 == 0)
{
return x_440;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_440, 0);
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_440);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
else
{
lean_object* x_445; uint8_t x_446; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_445 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_410);
x_446 = !lean_is_exclusive(x_445);
if (x_446 == 0)
{
return x_445;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_445, 0);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_445);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
}
else
{
lean_object* x_450; uint8_t x_451; lean_object* x_673; uint8_t x_674; 
x_450 = l_Lean_Syntax_getArg(x_348, x_87);
lean_dec(x_348);
x_673 = l_Lean_nullKind___closed__2;
lean_inc(x_450);
x_674 = l_Lean_Syntax_isOfKind(x_450, x_673);
if (x_674 == 0)
{
uint8_t x_675; 
x_675 = 0;
x_451 = x_675;
goto block_672;
}
else
{
lean_object* x_676; lean_object* x_677; uint8_t x_678; 
x_676 = l_Lean_Syntax_getArgs(x_450);
x_677 = lean_array_get_size(x_676);
lean_dec(x_676);
x_678 = lean_nat_dec_eq(x_677, x_87);
lean_dec(x_677);
x_451 = x_678;
goto block_672;
}
block_672:
{
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_450);
lean_dec(x_346);
lean_dec(x_242);
x_452 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_st_ref_get(x_8, x_454);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_ctor_get(x_456, 0);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_st_ref_get(x_4, x_457);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_ctor_get(x_460, 5);
lean_inc(x_462);
lean_dec(x_460);
x_463 = lean_ctor_get(x_7, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_7, 2);
lean_inc(x_464);
x_465 = lean_environment_main_module(x_458);
x_466 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_453);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_464);
lean_inc(x_1);
x_467 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_466, x_462);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_st_ref_take(x_4, x_461);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = !lean_is_exclusive(x_471);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_471, 5);
lean_dec(x_474);
lean_ctor_set(x_471, 5, x_469);
x_475 = lean_st_ref_set(x_4, x_471, x_472);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
lean_dec(x_475);
x_10 = x_468;
x_11 = x_476;
goto block_36;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_477 = lean_ctor_get(x_471, 0);
x_478 = lean_ctor_get(x_471, 1);
x_479 = lean_ctor_get(x_471, 2);
x_480 = lean_ctor_get(x_471, 3);
x_481 = lean_ctor_get(x_471, 4);
x_482 = lean_ctor_get(x_471, 6);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_471);
x_483 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_483, 0, x_477);
lean_ctor_set(x_483, 1, x_478);
lean_ctor_set(x_483, 2, x_479);
lean_ctor_set(x_483, 3, x_480);
lean_ctor_set(x_483, 4, x_481);
lean_ctor_set(x_483, 5, x_469);
lean_ctor_set(x_483, 6, x_482);
x_484 = lean_st_ref_set(x_4, x_483, x_472);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
x_10 = x_468;
x_11 = x_485;
goto block_36;
}
}
else
{
lean_object* x_486; 
lean_dec(x_2);
lean_dec(x_1);
x_486 = lean_ctor_get(x_467, 0);
lean_inc(x_486);
lean_dec(x_467);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_489, 0, x_488);
x_490 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_490, 0, x_489);
x_491 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_487, x_490, x_3, x_4, x_5, x_6, x_7, x_8, x_461);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_487);
x_492 = !lean_is_exclusive(x_491);
if (x_492 == 0)
{
return x_491;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_491, 0);
x_494 = lean_ctor_get(x_491, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_491);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
else
{
lean_object* x_496; uint8_t x_497; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_496 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_461);
x_497 = !lean_is_exclusive(x_496);
if (x_497 == 0)
{
return x_496;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_496, 0);
x_499 = lean_ctor_get(x_496, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_496);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
}
else
{
lean_object* x_501; uint8_t x_502; lean_object* x_665; uint8_t x_666; 
x_501 = l_Lean_Syntax_getArg(x_450, x_139);
lean_dec(x_450);
x_665 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_501);
x_666 = l_Lean_Syntax_isOfKind(x_501, x_665);
if (x_666 == 0)
{
uint8_t x_667; 
x_667 = 0;
x_502 = x_667;
goto block_664;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
x_668 = l_Lean_Syntax_getArgs(x_501);
x_669 = lean_array_get_size(x_668);
lean_dec(x_668);
x_670 = lean_unsigned_to_nat(3u);
x_671 = lean_nat_dec_eq(x_669, x_670);
lean_dec(x_669);
x_502 = x_671;
goto block_664;
}
block_664:
{
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_501);
lean_dec(x_346);
lean_dec(x_242);
x_503 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = lean_st_ref_get(x_8, x_505);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_ctor_get(x_507, 0);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_st_ref_get(x_4, x_508);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_ctor_get(x_511, 5);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_ctor_get(x_7, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_7, 2);
lean_inc(x_515);
x_516 = lean_environment_main_module(x_509);
x_517 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_504);
lean_ctor_set(x_517, 2, x_514);
lean_ctor_set(x_517, 3, x_515);
lean_inc(x_1);
x_518 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_517, x_513);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = lean_st_ref_take(x_4, x_512);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = !lean_is_exclusive(x_522);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_522, 5);
lean_dec(x_525);
lean_ctor_set(x_522, 5, x_520);
x_526 = lean_st_ref_set(x_4, x_522, x_523);
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
lean_dec(x_526);
x_10 = x_519;
x_11 = x_527;
goto block_36;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_528 = lean_ctor_get(x_522, 0);
x_529 = lean_ctor_get(x_522, 1);
x_530 = lean_ctor_get(x_522, 2);
x_531 = lean_ctor_get(x_522, 3);
x_532 = lean_ctor_get(x_522, 4);
x_533 = lean_ctor_get(x_522, 6);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_530);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_522);
x_534 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_534, 0, x_528);
lean_ctor_set(x_534, 1, x_529);
lean_ctor_set(x_534, 2, x_530);
lean_ctor_set(x_534, 3, x_531);
lean_ctor_set(x_534, 4, x_532);
lean_ctor_set(x_534, 5, x_520);
lean_ctor_set(x_534, 6, x_533);
x_535 = lean_st_ref_set(x_4, x_534, x_523);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_10 = x_519;
x_11 = x_536;
goto block_36;
}
}
else
{
lean_object* x_537; 
lean_dec(x_2);
lean_dec(x_1);
x_537 = lean_ctor_get(x_518, 0);
lean_inc(x_537);
lean_dec(x_518);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_540, 0, x_539);
x_541 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_541, 0, x_540);
x_542 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_538, x_541, x_3, x_4, x_5, x_6, x_7, x_8, x_512);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_538);
x_543 = !lean_is_exclusive(x_542);
if (x_543 == 0)
{
return x_542;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_542, 0);
x_545 = lean_ctor_get(x_542, 1);
lean_inc(x_545);
lean_inc(x_544);
lean_dec(x_542);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
return x_546;
}
}
else
{
lean_object* x_547; uint8_t x_548; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_547 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_512);
x_548 = !lean_is_exclusive(x_547);
if (x_548 == 0)
{
return x_547;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_547, 0);
x_550 = lean_ctor_get(x_547, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_547);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
}
}
else
{
lean_object* x_552; uint8_t x_553; lean_object* x_658; uint8_t x_659; 
x_552 = l_Lean_Syntax_getArg(x_501, x_139);
x_658 = l_Lean_nullKind___closed__2;
lean_inc(x_552);
x_659 = l_Lean_Syntax_isOfKind(x_552, x_658);
if (x_659 == 0)
{
uint8_t x_660; 
x_660 = 0;
x_553 = x_660;
goto block_657;
}
else
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_661 = l_Lean_Syntax_getArgs(x_552);
x_662 = lean_array_get_size(x_661);
lean_dec(x_661);
x_663 = lean_nat_dec_eq(x_662, x_87);
lean_dec(x_662);
x_553 = x_663;
goto block_657;
}
block_657:
{
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_552);
lean_dec(x_501);
lean_dec(x_346);
lean_dec(x_242);
x_554 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_st_ref_get(x_8, x_556);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_st_ref_get(x_4, x_559);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = lean_ctor_get(x_562, 5);
lean_inc(x_564);
lean_dec(x_562);
x_565 = lean_ctor_get(x_7, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_7, 2);
lean_inc(x_566);
x_567 = lean_environment_main_module(x_560);
x_568 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_555);
lean_ctor_set(x_568, 2, x_565);
lean_ctor_set(x_568, 3, x_566);
lean_inc(x_1);
x_569 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_568, x_564);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_572 = lean_st_ref_take(x_4, x_563);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = !lean_is_exclusive(x_573);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_573, 5);
lean_dec(x_576);
lean_ctor_set(x_573, 5, x_571);
x_577 = lean_st_ref_set(x_4, x_573, x_574);
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
lean_dec(x_577);
x_10 = x_570;
x_11 = x_578;
goto block_36;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_579 = lean_ctor_get(x_573, 0);
x_580 = lean_ctor_get(x_573, 1);
x_581 = lean_ctor_get(x_573, 2);
x_582 = lean_ctor_get(x_573, 3);
x_583 = lean_ctor_get(x_573, 4);
x_584 = lean_ctor_get(x_573, 6);
lean_inc(x_584);
lean_inc(x_583);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_573);
x_585 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_585, 0, x_579);
lean_ctor_set(x_585, 1, x_580);
lean_ctor_set(x_585, 2, x_581);
lean_ctor_set(x_585, 3, x_582);
lean_ctor_set(x_585, 4, x_583);
lean_ctor_set(x_585, 5, x_571);
lean_ctor_set(x_585, 6, x_584);
x_586 = lean_st_ref_set(x_4, x_585, x_574);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
x_10 = x_570;
x_11 = x_587;
goto block_36;
}
}
else
{
lean_object* x_588; 
lean_dec(x_2);
lean_dec(x_1);
x_588 = lean_ctor_get(x_569, 0);
lean_inc(x_588);
lean_dec(x_569);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
x_591 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_591, 0, x_590);
x_592 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_592, 0, x_591);
x_593 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_589, x_592, x_3, x_4, x_5, x_6, x_7, x_8, x_563);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_589);
x_594 = !lean_is_exclusive(x_593);
if (x_594 == 0)
{
return x_593;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_595 = lean_ctor_get(x_593, 0);
x_596 = lean_ctor_get(x_593, 1);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_593);
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_595);
lean_ctor_set(x_597, 1, x_596);
return x_597;
}
}
else
{
lean_object* x_598; uint8_t x_599; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_598 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_563);
x_599 = !lean_is_exclusive(x_598);
if (x_599 == 0)
{
return x_598;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_598, 0);
x_601 = lean_ctor_get(x_598, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_598);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
}
else
{
lean_object* x_603; lean_object* x_604; uint8_t x_605; 
x_603 = l_Lean_Syntax_getArg(x_552, x_139);
lean_dec(x_552);
x_604 = l_Lean_identKind___closed__2;
lean_inc(x_603);
x_605 = l_Lean_Syntax_isOfKind(x_603, x_604);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_603);
lean_dec(x_501);
lean_dec(x_346);
lean_dec(x_242);
x_606 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_st_ref_get(x_8, x_608);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_ctor_get(x_610, 0);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_st_ref_get(x_4, x_611);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_ctor_get(x_614, 5);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_ctor_get(x_7, 1);
lean_inc(x_617);
x_618 = lean_ctor_get(x_7, 2);
lean_inc(x_618);
x_619 = lean_environment_main_module(x_612);
x_620 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_607);
lean_ctor_set(x_620, 2, x_617);
lean_ctor_set(x_620, 3, x_618);
lean_inc(x_1);
x_621 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_620, x_616);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_st_ref_take(x_4, x_615);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = !lean_is_exclusive(x_625);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_625, 5);
lean_dec(x_628);
lean_ctor_set(x_625, 5, x_623);
x_629 = lean_st_ref_set(x_4, x_625, x_626);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec(x_629);
x_10 = x_622;
x_11 = x_630;
goto block_36;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_631 = lean_ctor_get(x_625, 0);
x_632 = lean_ctor_get(x_625, 1);
x_633 = lean_ctor_get(x_625, 2);
x_634 = lean_ctor_get(x_625, 3);
x_635 = lean_ctor_get(x_625, 4);
x_636 = lean_ctor_get(x_625, 6);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
lean_inc(x_633);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_625);
x_637 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_637, 0, x_631);
lean_ctor_set(x_637, 1, x_632);
lean_ctor_set(x_637, 2, x_633);
lean_ctor_set(x_637, 3, x_634);
lean_ctor_set(x_637, 4, x_635);
lean_ctor_set(x_637, 5, x_623);
lean_ctor_set(x_637, 6, x_636);
x_638 = lean_st_ref_set(x_4, x_637, x_626);
x_639 = lean_ctor_get(x_638, 1);
lean_inc(x_639);
lean_dec(x_638);
x_10 = x_622;
x_11 = x_639;
goto block_36;
}
}
else
{
lean_object* x_640; 
lean_dec(x_2);
lean_dec(x_1);
x_640 = lean_ctor_get(x_621, 0);
lean_inc(x_640);
lean_dec(x_621);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_641, x_644, x_3, x_4, x_5, x_6, x_7, x_8, x_615);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_641);
x_646 = !lean_is_exclusive(x_645);
if (x_646 == 0)
{
return x_645;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_647 = lean_ctor_get(x_645, 0);
x_648 = lean_ctor_get(x_645, 1);
lean_inc(x_648);
lean_inc(x_647);
lean_dec(x_645);
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_648);
return x_649;
}
}
else
{
lean_object* x_650; uint8_t x_651; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_650 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_615);
x_651 = !lean_is_exclusive(x_650);
if (x_651 == 0)
{
return x_650;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_650, 0);
x_653 = lean_ctor_get(x_650, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_650);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
}
else
{
lean_object* x_655; lean_object* x_656; 
x_655 = l_Lean_Syntax_getArg(x_501, x_243);
lean_dec(x_501);
x_656 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_242, x_603, x_346, x_655, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_656;
}
}
}
}
}
}
}
}
}
block_914:
{
if (x_682 == 0)
{
if (x_681 == 0)
{
uint8_t x_683; 
lean_dec(x_399);
x_683 = 0;
x_400 = x_683;
goto block_679;
}
else
{
lean_object* x_684; lean_object* x_685; uint8_t x_686; 
x_684 = l_Lean_Syntax_getArgs(x_399);
lean_dec(x_399);
x_685 = lean_array_get_size(x_684);
lean_dec(x_684);
x_686 = lean_nat_dec_eq(x_685, x_87);
lean_dec(x_685);
x_400 = x_686;
goto block_679;
}
}
else
{
lean_object* x_687; uint8_t x_688; uint8_t x_909; 
lean_dec(x_399);
x_687 = l_Lean_Syntax_getArg(x_348, x_87);
lean_dec(x_348);
lean_inc(x_687);
x_909 = l_Lean_Syntax_isOfKind(x_687, x_680);
if (x_909 == 0)
{
uint8_t x_910; 
x_910 = 0;
x_688 = x_910;
goto block_908;
}
else
{
lean_object* x_911; lean_object* x_912; uint8_t x_913; 
x_911 = l_Lean_Syntax_getArgs(x_687);
x_912 = lean_array_get_size(x_911);
lean_dec(x_911);
x_913 = lean_nat_dec_eq(x_912, x_87);
lean_dec(x_912);
x_688 = x_913;
goto block_908;
}
block_908:
{
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_687);
lean_dec(x_346);
lean_dec(x_242);
x_689 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_st_ref_get(x_8, x_691);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
x_695 = lean_ctor_get(x_693, 0);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_st_ref_get(x_4, x_694);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_ctor_get(x_697, 5);
lean_inc(x_699);
lean_dec(x_697);
x_700 = lean_ctor_get(x_7, 1);
lean_inc(x_700);
x_701 = lean_ctor_get(x_7, 2);
lean_inc(x_701);
x_702 = lean_environment_main_module(x_695);
x_703 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_690);
lean_ctor_set(x_703, 2, x_700);
lean_ctor_set(x_703, 3, x_701);
lean_inc(x_1);
x_704 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_703, x_699);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; uint8_t x_710; 
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
lean_dec(x_704);
x_707 = lean_st_ref_take(x_4, x_698);
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_710 = !lean_is_exclusive(x_708);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_708, 5);
lean_dec(x_711);
lean_ctor_set(x_708, 5, x_706);
x_712 = lean_st_ref_set(x_4, x_708, x_709);
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
lean_dec(x_712);
x_10 = x_705;
x_11 = x_713;
goto block_36;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_714 = lean_ctor_get(x_708, 0);
x_715 = lean_ctor_get(x_708, 1);
x_716 = lean_ctor_get(x_708, 2);
x_717 = lean_ctor_get(x_708, 3);
x_718 = lean_ctor_get(x_708, 4);
x_719 = lean_ctor_get(x_708, 6);
lean_inc(x_719);
lean_inc(x_718);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_708);
x_720 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_720, 0, x_714);
lean_ctor_set(x_720, 1, x_715);
lean_ctor_set(x_720, 2, x_716);
lean_ctor_set(x_720, 3, x_717);
lean_ctor_set(x_720, 4, x_718);
lean_ctor_set(x_720, 5, x_706);
lean_ctor_set(x_720, 6, x_719);
x_721 = lean_st_ref_set(x_4, x_720, x_709);
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
x_10 = x_705;
x_11 = x_722;
goto block_36;
}
}
else
{
lean_object* x_723; 
lean_dec(x_2);
lean_dec(x_1);
x_723 = lean_ctor_get(x_704, 0);
lean_inc(x_723);
lean_dec(x_704);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_726 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_726, 0, x_725);
x_727 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_727, 0, x_726);
x_728 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_724, x_727, x_3, x_4, x_5, x_6, x_7, x_8, x_698);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_724);
x_729 = !lean_is_exclusive(x_728);
if (x_729 == 0)
{
return x_728;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_728, 0);
x_731 = lean_ctor_get(x_728, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_728);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
else
{
lean_object* x_733; uint8_t x_734; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_733 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_698);
x_734 = !lean_is_exclusive(x_733);
if (x_734 == 0)
{
return x_733;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_733, 0);
x_736 = lean_ctor_get(x_733, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_733);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
}
}
else
{
lean_object* x_738; uint8_t x_739; lean_object* x_901; uint8_t x_902; 
x_738 = l_Lean_Syntax_getArg(x_687, x_139);
lean_dec(x_687);
x_901 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_738);
x_902 = l_Lean_Syntax_isOfKind(x_738, x_901);
if (x_902 == 0)
{
uint8_t x_903; 
x_903 = 0;
x_739 = x_903;
goto block_900;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; 
x_904 = l_Lean_Syntax_getArgs(x_738);
x_905 = lean_array_get_size(x_904);
lean_dec(x_904);
x_906 = lean_unsigned_to_nat(3u);
x_907 = lean_nat_dec_eq(x_905, x_906);
lean_dec(x_905);
x_739 = x_907;
goto block_900;
}
block_900:
{
if (x_739 == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_738);
lean_dec(x_346);
lean_dec(x_242);
x_740 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec(x_740);
x_743 = lean_st_ref_get(x_8, x_742);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_ctor_get(x_744, 0);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_st_ref_get(x_4, x_745);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
x_750 = lean_ctor_get(x_748, 5);
lean_inc(x_750);
lean_dec(x_748);
x_751 = lean_ctor_get(x_7, 1);
lean_inc(x_751);
x_752 = lean_ctor_get(x_7, 2);
lean_inc(x_752);
x_753 = lean_environment_main_module(x_746);
x_754 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_741);
lean_ctor_set(x_754, 2, x_751);
lean_ctor_set(x_754, 3, x_752);
lean_inc(x_1);
x_755 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_754, x_750);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
x_758 = lean_st_ref_take(x_4, x_749);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = !lean_is_exclusive(x_759);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_762 = lean_ctor_get(x_759, 5);
lean_dec(x_762);
lean_ctor_set(x_759, 5, x_757);
x_763 = lean_st_ref_set(x_4, x_759, x_760);
x_764 = lean_ctor_get(x_763, 1);
lean_inc(x_764);
lean_dec(x_763);
x_10 = x_756;
x_11 = x_764;
goto block_36;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_765 = lean_ctor_get(x_759, 0);
x_766 = lean_ctor_get(x_759, 1);
x_767 = lean_ctor_get(x_759, 2);
x_768 = lean_ctor_get(x_759, 3);
x_769 = lean_ctor_get(x_759, 4);
x_770 = lean_ctor_get(x_759, 6);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_inc(x_766);
lean_inc(x_765);
lean_dec(x_759);
x_771 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_771, 0, x_765);
lean_ctor_set(x_771, 1, x_766);
lean_ctor_set(x_771, 2, x_767);
lean_ctor_set(x_771, 3, x_768);
lean_ctor_set(x_771, 4, x_769);
lean_ctor_set(x_771, 5, x_757);
lean_ctor_set(x_771, 6, x_770);
x_772 = lean_st_ref_set(x_4, x_771, x_760);
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
lean_dec(x_772);
x_10 = x_756;
x_11 = x_773;
goto block_36;
}
}
else
{
lean_object* x_774; 
lean_dec(x_2);
lean_dec(x_1);
x_774 = lean_ctor_get(x_755, 0);
lean_inc(x_774);
lean_dec(x_755);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_777 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_777, 0, x_776);
x_778 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_778, 0, x_777);
x_779 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_775, x_778, x_3, x_4, x_5, x_6, x_7, x_8, x_749);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_775);
x_780 = !lean_is_exclusive(x_779);
if (x_780 == 0)
{
return x_779;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_781 = lean_ctor_get(x_779, 0);
x_782 = lean_ctor_get(x_779, 1);
lean_inc(x_782);
lean_inc(x_781);
lean_dec(x_779);
x_783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_783, 0, x_781);
lean_ctor_set(x_783, 1, x_782);
return x_783;
}
}
else
{
lean_object* x_784; uint8_t x_785; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_784 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_749);
x_785 = !lean_is_exclusive(x_784);
if (x_785 == 0)
{
return x_784;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_784, 0);
x_787 = lean_ctor_get(x_784, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_784);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
}
else
{
lean_object* x_789; uint8_t x_790; uint8_t x_895; 
x_789 = l_Lean_Syntax_getArg(x_738, x_139);
lean_inc(x_789);
x_895 = l_Lean_Syntax_isOfKind(x_789, x_680);
if (x_895 == 0)
{
uint8_t x_896; 
x_896 = 0;
x_790 = x_896;
goto block_894;
}
else
{
lean_object* x_897; lean_object* x_898; uint8_t x_899; 
x_897 = l_Lean_Syntax_getArgs(x_789);
x_898 = lean_array_get_size(x_897);
lean_dec(x_897);
x_899 = lean_nat_dec_eq(x_898, x_87);
lean_dec(x_898);
x_790 = x_899;
goto block_894;
}
block_894:
{
if (x_790 == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_789);
lean_dec(x_738);
lean_dec(x_346);
lean_dec(x_242);
x_791 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
x_794 = lean_st_ref_get(x_8, x_793);
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = lean_ctor_get(x_795, 0);
lean_inc(x_797);
lean_dec(x_795);
x_798 = lean_st_ref_get(x_4, x_796);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
lean_dec(x_798);
x_801 = lean_ctor_get(x_799, 5);
lean_inc(x_801);
lean_dec(x_799);
x_802 = lean_ctor_get(x_7, 1);
lean_inc(x_802);
x_803 = lean_ctor_get(x_7, 2);
lean_inc(x_803);
x_804 = lean_environment_main_module(x_797);
x_805 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_792);
lean_ctor_set(x_805, 2, x_802);
lean_ctor_set(x_805, 3, x_803);
lean_inc(x_1);
x_806 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_805, x_801);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec(x_806);
x_809 = lean_st_ref_take(x_4, x_800);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
x_812 = !lean_is_exclusive(x_810);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_810, 5);
lean_dec(x_813);
lean_ctor_set(x_810, 5, x_808);
x_814 = lean_st_ref_set(x_4, x_810, x_811);
x_815 = lean_ctor_get(x_814, 1);
lean_inc(x_815);
lean_dec(x_814);
x_10 = x_807;
x_11 = x_815;
goto block_36;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_816 = lean_ctor_get(x_810, 0);
x_817 = lean_ctor_get(x_810, 1);
x_818 = lean_ctor_get(x_810, 2);
x_819 = lean_ctor_get(x_810, 3);
x_820 = lean_ctor_get(x_810, 4);
x_821 = lean_ctor_get(x_810, 6);
lean_inc(x_821);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_810);
x_822 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_822, 0, x_816);
lean_ctor_set(x_822, 1, x_817);
lean_ctor_set(x_822, 2, x_818);
lean_ctor_set(x_822, 3, x_819);
lean_ctor_set(x_822, 4, x_820);
lean_ctor_set(x_822, 5, x_808);
lean_ctor_set(x_822, 6, x_821);
x_823 = lean_st_ref_set(x_4, x_822, x_811);
x_824 = lean_ctor_get(x_823, 1);
lean_inc(x_824);
lean_dec(x_823);
x_10 = x_807;
x_11 = x_824;
goto block_36;
}
}
else
{
lean_object* x_825; 
lean_dec(x_2);
lean_dec(x_1);
x_825 = lean_ctor_get(x_806, 0);
lean_inc(x_825);
lean_dec(x_806);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_828, 0, x_827);
x_829 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_829, 0, x_828);
x_830 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_826, x_829, x_3, x_4, x_5, x_6, x_7, x_8, x_800);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_826);
x_831 = !lean_is_exclusive(x_830);
if (x_831 == 0)
{
return x_830;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_830, 0);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_inc(x_832);
lean_dec(x_830);
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_833);
return x_834;
}
}
else
{
lean_object* x_835; uint8_t x_836; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_835 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_800);
x_836 = !lean_is_exclusive(x_835);
if (x_836 == 0)
{
return x_835;
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_837 = lean_ctor_get(x_835, 0);
x_838 = lean_ctor_get(x_835, 1);
lean_inc(x_838);
lean_inc(x_837);
lean_dec(x_835);
x_839 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set(x_839, 1, x_838);
return x_839;
}
}
}
}
else
{
lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_840 = l_Lean_Syntax_getArg(x_789, x_139);
lean_dec(x_789);
x_841 = l_Lean_identKind___closed__2;
lean_inc(x_840);
x_842 = l_Lean_Syntax_isOfKind(x_840, x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_840);
lean_dec(x_738);
lean_dec(x_346);
lean_dec(x_242);
x_843 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
lean_dec(x_843);
x_846 = lean_st_ref_get(x_8, x_845);
x_847 = lean_ctor_get(x_846, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_846, 1);
lean_inc(x_848);
lean_dec(x_846);
x_849 = lean_ctor_get(x_847, 0);
lean_inc(x_849);
lean_dec(x_847);
x_850 = lean_st_ref_get(x_4, x_848);
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
lean_dec(x_850);
x_853 = lean_ctor_get(x_851, 5);
lean_inc(x_853);
lean_dec(x_851);
x_854 = lean_ctor_get(x_7, 1);
lean_inc(x_854);
x_855 = lean_ctor_get(x_7, 2);
lean_inc(x_855);
x_856 = lean_environment_main_module(x_849);
x_857 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_844);
lean_ctor_set(x_857, 2, x_854);
lean_ctor_set(x_857, 3, x_855);
lean_inc(x_1);
x_858 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_857, x_853);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = lean_st_ref_take(x_4, x_852);
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_864 = !lean_is_exclusive(x_862);
if (x_864 == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_862, 5);
lean_dec(x_865);
lean_ctor_set(x_862, 5, x_860);
x_866 = lean_st_ref_set(x_4, x_862, x_863);
x_867 = lean_ctor_get(x_866, 1);
lean_inc(x_867);
lean_dec(x_866);
x_10 = x_859;
x_11 = x_867;
goto block_36;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_868 = lean_ctor_get(x_862, 0);
x_869 = lean_ctor_get(x_862, 1);
x_870 = lean_ctor_get(x_862, 2);
x_871 = lean_ctor_get(x_862, 3);
x_872 = lean_ctor_get(x_862, 4);
x_873 = lean_ctor_get(x_862, 6);
lean_inc(x_873);
lean_inc(x_872);
lean_inc(x_871);
lean_inc(x_870);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_862);
x_874 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_874, 0, x_868);
lean_ctor_set(x_874, 1, x_869);
lean_ctor_set(x_874, 2, x_870);
lean_ctor_set(x_874, 3, x_871);
lean_ctor_set(x_874, 4, x_872);
lean_ctor_set(x_874, 5, x_860);
lean_ctor_set(x_874, 6, x_873);
x_875 = lean_st_ref_set(x_4, x_874, x_863);
x_876 = lean_ctor_get(x_875, 1);
lean_inc(x_876);
lean_dec(x_875);
x_10 = x_859;
x_11 = x_876;
goto block_36;
}
}
else
{
lean_object* x_877; 
lean_dec(x_2);
lean_dec(x_1);
x_877 = lean_ctor_get(x_858, 0);
lean_inc(x_877);
lean_dec(x_858);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_883; 
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_880, 0, x_879);
x_881 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_881, 0, x_880);
x_882 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_878, x_881, x_3, x_4, x_5, x_6, x_7, x_8, x_852);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_878);
x_883 = !lean_is_exclusive(x_882);
if (x_883 == 0)
{
return x_882;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_882, 0);
x_885 = lean_ctor_get(x_882, 1);
lean_inc(x_885);
lean_inc(x_884);
lean_dec(x_882);
x_886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set(x_886, 1, x_885);
return x_886;
}
}
else
{
lean_object* x_887; uint8_t x_888; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_887 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_852);
x_888 = !lean_is_exclusive(x_887);
if (x_888 == 0)
{
return x_887;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_889 = lean_ctor_get(x_887, 0);
x_890 = lean_ctor_get(x_887, 1);
lean_inc(x_890);
lean_inc(x_889);
lean_dec(x_887);
x_891 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
return x_891;
}
}
}
}
else
{
lean_object* x_892; lean_object* x_893; 
x_892 = l_Lean_Syntax_getArg(x_738, x_243);
lean_dec(x_738);
x_893 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_242, x_840, x_346, x_892, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_893;
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
block_1517:
{
if (x_936 == 0)
{
if (x_935 == 0)
{
uint8_t x_937; 
x_937 = 0;
x_245 = x_937;
goto block_933;
}
else
{
lean_object* x_938; lean_object* x_939; uint8_t x_940; 
x_938 = l_Lean_Syntax_getArgs(x_244);
x_939 = lean_array_get_size(x_938);
lean_dec(x_938);
x_940 = lean_nat_dec_eq(x_939, x_87);
lean_dec(x_939);
x_245 = x_940;
goto block_933;
}
}
else
{
lean_object* x_941; lean_object* x_942; uint8_t x_943; lean_object* x_1511; uint8_t x_1512; 
lean_dec(x_244);
x_941 = lean_unsigned_to_nat(4u);
x_942 = l_Lean_Syntax_getArg(x_1, x_941);
x_1511 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__11;
lean_inc(x_942);
x_1512 = l_Lean_Syntax_isOfKind(x_942, x_1511);
if (x_1512 == 0)
{
uint8_t x_1513; 
x_1513 = 0;
x_943 = x_1513;
goto block_1510;
}
else
{
lean_object* x_1514; lean_object* x_1515; uint8_t x_1516; 
x_1514 = l_Lean_Syntax_getArgs(x_942);
x_1515 = lean_array_get_size(x_1514);
lean_dec(x_1514);
x_1516 = lean_nat_dec_eq(x_1515, x_243);
lean_dec(x_1515);
x_943 = x_1516;
goto block_1510;
}
block_1510:
{
if (x_943 == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
lean_dec(x_942);
lean_dec(x_242);
x_944 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
x_947 = lean_st_ref_get(x_8, x_946);
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
lean_dec(x_947);
x_950 = lean_ctor_get(x_948, 0);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_st_ref_get(x_4, x_949);
x_952 = lean_ctor_get(x_951, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec(x_951);
x_954 = lean_ctor_get(x_952, 5);
lean_inc(x_954);
lean_dec(x_952);
x_955 = lean_ctor_get(x_7, 1);
lean_inc(x_955);
x_956 = lean_ctor_get(x_7, 2);
lean_inc(x_956);
x_957 = lean_environment_main_module(x_950);
x_958 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_958, 0, x_957);
lean_ctor_set(x_958, 1, x_945);
lean_ctor_set(x_958, 2, x_955);
lean_ctor_set(x_958, 3, x_956);
lean_inc(x_1);
x_959 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_958, x_954);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; 
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
lean_dec(x_959);
x_962 = lean_st_ref_take(x_4, x_953);
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
lean_dec(x_962);
x_965 = !lean_is_exclusive(x_963);
if (x_965 == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_963, 5);
lean_dec(x_966);
lean_ctor_set(x_963, 5, x_961);
x_967 = lean_st_ref_set(x_4, x_963, x_964);
x_968 = lean_ctor_get(x_967, 1);
lean_inc(x_968);
lean_dec(x_967);
x_10 = x_960;
x_11 = x_968;
goto block_36;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_969 = lean_ctor_get(x_963, 0);
x_970 = lean_ctor_get(x_963, 1);
x_971 = lean_ctor_get(x_963, 2);
x_972 = lean_ctor_get(x_963, 3);
x_973 = lean_ctor_get(x_963, 4);
x_974 = lean_ctor_get(x_963, 6);
lean_inc(x_974);
lean_inc(x_973);
lean_inc(x_972);
lean_inc(x_971);
lean_inc(x_970);
lean_inc(x_969);
lean_dec(x_963);
x_975 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_975, 0, x_969);
lean_ctor_set(x_975, 1, x_970);
lean_ctor_set(x_975, 2, x_971);
lean_ctor_set(x_975, 3, x_972);
lean_ctor_set(x_975, 4, x_973);
lean_ctor_set(x_975, 5, x_961);
lean_ctor_set(x_975, 6, x_974);
x_976 = lean_st_ref_set(x_4, x_975, x_964);
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
lean_dec(x_976);
x_10 = x_960;
x_11 = x_977;
goto block_36;
}
}
else
{
lean_object* x_978; 
lean_dec(x_2);
lean_dec(x_1);
x_978 = lean_ctor_get(x_959, 0);
lean_inc(x_978);
lean_dec(x_959);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; uint8_t x_984; 
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_981 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_981, 0, x_980);
x_982 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_982, 0, x_981);
x_983 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_979, x_982, x_3, x_4, x_5, x_6, x_7, x_8, x_953);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_979);
x_984 = !lean_is_exclusive(x_983);
if (x_984 == 0)
{
return x_983;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_983, 0);
x_986 = lean_ctor_get(x_983, 1);
lean_inc(x_986);
lean_inc(x_985);
lean_dec(x_983);
x_987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_987, 0, x_985);
lean_ctor_set(x_987, 1, x_986);
return x_987;
}
}
else
{
lean_object* x_988; uint8_t x_989; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_988 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_953);
x_989 = !lean_is_exclusive(x_988);
if (x_989 == 0)
{
return x_988;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_988, 0);
x_991 = lean_ctor_get(x_988, 1);
lean_inc(x_991);
lean_inc(x_990);
lean_dec(x_988);
x_992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
return x_992;
}
}
}
}
else
{
lean_object* x_993; uint8_t x_994; uint8_t x_1272; uint8_t x_1273; 
x_993 = l_Lean_Syntax_getArg(x_942, x_139);
lean_inc(x_993);
x_1272 = l_Lean_Syntax_isOfKind(x_993, x_934);
if (x_1272 == 0)
{
uint8_t x_1506; 
x_1506 = 0;
x_1273 = x_1506;
goto block_1505;
}
else
{
lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; 
x_1507 = l_Lean_Syntax_getArgs(x_993);
x_1508 = lean_array_get_size(x_1507);
lean_dec(x_1507);
x_1509 = lean_nat_dec_eq(x_1508, x_139);
lean_dec(x_1508);
x_1273 = x_1509;
goto block_1505;
}
block_1271:
{
if (x_994 == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_942);
lean_dec(x_242);
x_995 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec(x_995);
x_998 = lean_st_ref_get(x_8, x_997);
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec(x_998);
x_1001 = lean_ctor_get(x_999, 0);
lean_inc(x_1001);
lean_dec(x_999);
x_1002 = lean_st_ref_get(x_4, x_1000);
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1002, 1);
lean_inc(x_1004);
lean_dec(x_1002);
x_1005 = lean_ctor_get(x_1003, 5);
lean_inc(x_1005);
lean_dec(x_1003);
x_1006 = lean_ctor_get(x_7, 1);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_7, 2);
lean_inc(x_1007);
x_1008 = lean_environment_main_module(x_1001);
x_1009 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1009, 1, x_996);
lean_ctor_set(x_1009, 2, x_1006);
lean_ctor_set(x_1009, 3, x_1007);
lean_inc(x_1);
x_1010 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1009, x_1005);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; uint8_t x_1016; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
x_1013 = lean_st_ref_take(x_4, x_1004);
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1013, 1);
lean_inc(x_1015);
lean_dec(x_1013);
x_1016 = !lean_is_exclusive(x_1014);
if (x_1016 == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_1014, 5);
lean_dec(x_1017);
lean_ctor_set(x_1014, 5, x_1012);
x_1018 = lean_st_ref_set(x_4, x_1014, x_1015);
x_1019 = lean_ctor_get(x_1018, 1);
lean_inc(x_1019);
lean_dec(x_1018);
x_10 = x_1011;
x_11 = x_1019;
goto block_36;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1020 = lean_ctor_get(x_1014, 0);
x_1021 = lean_ctor_get(x_1014, 1);
x_1022 = lean_ctor_get(x_1014, 2);
x_1023 = lean_ctor_get(x_1014, 3);
x_1024 = lean_ctor_get(x_1014, 4);
x_1025 = lean_ctor_get(x_1014, 6);
lean_inc(x_1025);
lean_inc(x_1024);
lean_inc(x_1023);
lean_inc(x_1022);
lean_inc(x_1021);
lean_inc(x_1020);
lean_dec(x_1014);
x_1026 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1026, 0, x_1020);
lean_ctor_set(x_1026, 1, x_1021);
lean_ctor_set(x_1026, 2, x_1022);
lean_ctor_set(x_1026, 3, x_1023);
lean_ctor_set(x_1026, 4, x_1024);
lean_ctor_set(x_1026, 5, x_1012);
lean_ctor_set(x_1026, 6, x_1025);
x_1027 = lean_st_ref_set(x_4, x_1026, x_1015);
x_1028 = lean_ctor_get(x_1027, 1);
lean_inc(x_1028);
lean_dec(x_1027);
x_10 = x_1011;
x_11 = x_1028;
goto block_36;
}
}
else
{
lean_object* x_1029; 
lean_dec(x_2);
lean_dec(x_1);
x_1029 = lean_ctor_get(x_1010, 0);
lean_inc(x_1029);
lean_dec(x_1010);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1032, 0, x_1031);
x_1033 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1033, 0, x_1032);
x_1034 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1030, x_1033, x_3, x_4, x_5, x_6, x_7, x_8, x_1004);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1030);
x_1035 = !lean_is_exclusive(x_1034);
if (x_1035 == 0)
{
return x_1034;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1034, 0);
x_1037 = lean_ctor_get(x_1034, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_1034);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
else
{
lean_object* x_1039; uint8_t x_1040; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1039 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1004);
x_1040 = !lean_is_exclusive(x_1039);
if (x_1040 == 0)
{
return x_1039;
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1041 = lean_ctor_get(x_1039, 0);
x_1042 = lean_ctor_get(x_1039, 1);
lean_inc(x_1042);
lean_inc(x_1041);
lean_dec(x_1039);
x_1043 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1043, 0, x_1041);
lean_ctor_set(x_1043, 1, x_1042);
return x_1043;
}
}
}
}
else
{
lean_object* x_1044; uint8_t x_1045; uint8_t x_1266; 
x_1044 = l_Lean_Syntax_getArg(x_942, x_87);
lean_dec(x_942);
lean_inc(x_1044);
x_1266 = l_Lean_Syntax_isOfKind(x_1044, x_934);
if (x_1266 == 0)
{
uint8_t x_1267; 
x_1267 = 0;
x_1045 = x_1267;
goto block_1265;
}
else
{
lean_object* x_1268; lean_object* x_1269; uint8_t x_1270; 
x_1268 = l_Lean_Syntax_getArgs(x_1044);
x_1269 = lean_array_get_size(x_1268);
lean_dec(x_1268);
x_1270 = lean_nat_dec_eq(x_1269, x_87);
lean_dec(x_1269);
x_1045 = x_1270;
goto block_1265;
}
block_1265:
{
if (x_1045 == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_1044);
lean_dec(x_242);
x_1046 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1049 = lean_st_ref_get(x_8, x_1048);
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1052 = lean_ctor_get(x_1050, 0);
lean_inc(x_1052);
lean_dec(x_1050);
x_1053 = lean_st_ref_get(x_4, x_1051);
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
lean_dec(x_1053);
x_1056 = lean_ctor_get(x_1054, 5);
lean_inc(x_1056);
lean_dec(x_1054);
x_1057 = lean_ctor_get(x_7, 1);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_7, 2);
lean_inc(x_1058);
x_1059 = lean_environment_main_module(x_1052);
x_1060 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1060, 0, x_1059);
lean_ctor_set(x_1060, 1, x_1047);
lean_ctor_set(x_1060, 2, x_1057);
lean_ctor_set(x_1060, 3, x_1058);
lean_inc(x_1);
x_1061 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1060, x_1056);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; uint8_t x_1067; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
x_1064 = lean_st_ref_take(x_4, x_1055);
x_1065 = lean_ctor_get(x_1064, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1064, 1);
lean_inc(x_1066);
lean_dec(x_1064);
x_1067 = !lean_is_exclusive(x_1065);
if (x_1067 == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1068 = lean_ctor_get(x_1065, 5);
lean_dec(x_1068);
lean_ctor_set(x_1065, 5, x_1063);
x_1069 = lean_st_ref_set(x_4, x_1065, x_1066);
x_1070 = lean_ctor_get(x_1069, 1);
lean_inc(x_1070);
lean_dec(x_1069);
x_10 = x_1062;
x_11 = x_1070;
goto block_36;
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1071 = lean_ctor_get(x_1065, 0);
x_1072 = lean_ctor_get(x_1065, 1);
x_1073 = lean_ctor_get(x_1065, 2);
x_1074 = lean_ctor_get(x_1065, 3);
x_1075 = lean_ctor_get(x_1065, 4);
x_1076 = lean_ctor_get(x_1065, 6);
lean_inc(x_1076);
lean_inc(x_1075);
lean_inc(x_1074);
lean_inc(x_1073);
lean_inc(x_1072);
lean_inc(x_1071);
lean_dec(x_1065);
x_1077 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1077, 0, x_1071);
lean_ctor_set(x_1077, 1, x_1072);
lean_ctor_set(x_1077, 2, x_1073);
lean_ctor_set(x_1077, 3, x_1074);
lean_ctor_set(x_1077, 4, x_1075);
lean_ctor_set(x_1077, 5, x_1063);
lean_ctor_set(x_1077, 6, x_1076);
x_1078 = lean_st_ref_set(x_4, x_1077, x_1066);
x_1079 = lean_ctor_get(x_1078, 1);
lean_inc(x_1079);
lean_dec(x_1078);
x_10 = x_1062;
x_11 = x_1079;
goto block_36;
}
}
else
{
lean_object* x_1080; 
lean_dec(x_2);
lean_dec(x_1);
x_1080 = lean_ctor_get(x_1061, 0);
lean_inc(x_1080);
lean_dec(x_1061);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; uint8_t x_1086; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1083, 0, x_1082);
x_1084 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1084, 0, x_1083);
x_1085 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1081, x_1084, x_3, x_4, x_5, x_6, x_7, x_8, x_1055);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1081);
x_1086 = !lean_is_exclusive(x_1085);
if (x_1086 == 0)
{
return x_1085;
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1087 = lean_ctor_get(x_1085, 0);
x_1088 = lean_ctor_get(x_1085, 1);
lean_inc(x_1088);
lean_inc(x_1087);
lean_dec(x_1085);
x_1089 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1089, 0, x_1087);
lean_ctor_set(x_1089, 1, x_1088);
return x_1089;
}
}
else
{
lean_object* x_1090; uint8_t x_1091; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1090 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1055);
x_1091 = !lean_is_exclusive(x_1090);
if (x_1091 == 0)
{
return x_1090;
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1092 = lean_ctor_get(x_1090, 0);
x_1093 = lean_ctor_get(x_1090, 1);
lean_inc(x_1093);
lean_inc(x_1092);
lean_dec(x_1090);
x_1094 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1094, 0, x_1092);
lean_ctor_set(x_1094, 1, x_1093);
return x_1094;
}
}
}
}
else
{
lean_object* x_1095; uint8_t x_1096; lean_object* x_1258; uint8_t x_1259; 
x_1095 = l_Lean_Syntax_getArg(x_1044, x_139);
lean_dec(x_1044);
x_1258 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_1095);
x_1259 = l_Lean_Syntax_isOfKind(x_1095, x_1258);
if (x_1259 == 0)
{
uint8_t x_1260; 
x_1260 = 0;
x_1096 = x_1260;
goto block_1257;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; uint8_t x_1264; 
x_1261 = l_Lean_Syntax_getArgs(x_1095);
x_1262 = lean_array_get_size(x_1261);
lean_dec(x_1261);
x_1263 = lean_unsigned_to_nat(3u);
x_1264 = lean_nat_dec_eq(x_1262, x_1263);
lean_dec(x_1262);
x_1096 = x_1264;
goto block_1257;
}
block_1257:
{
if (x_1096 == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_1095);
lean_dec(x_242);
x_1097 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1097, 1);
lean_inc(x_1099);
lean_dec(x_1097);
x_1100 = lean_st_ref_get(x_8, x_1099);
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = lean_ctor_get(x_1101, 0);
lean_inc(x_1103);
lean_dec(x_1101);
x_1104 = lean_st_ref_get(x_4, x_1102);
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1104, 1);
lean_inc(x_1106);
lean_dec(x_1104);
x_1107 = lean_ctor_get(x_1105, 5);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = lean_ctor_get(x_7, 1);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_7, 2);
lean_inc(x_1109);
x_1110 = lean_environment_main_module(x_1103);
x_1111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1111, 0, x_1110);
lean_ctor_set(x_1111, 1, x_1098);
lean_ctor_set(x_1111, 2, x_1108);
lean_ctor_set(x_1111, 3, x_1109);
lean_inc(x_1);
x_1112 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1111, x_1107);
if (lean_obj_tag(x_1112) == 0)
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; uint8_t x_1118; 
x_1113 = lean_ctor_get(x_1112, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1112, 1);
lean_inc(x_1114);
lean_dec(x_1112);
x_1115 = lean_st_ref_take(x_4, x_1106);
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
x_1118 = !lean_is_exclusive(x_1116);
if (x_1118 == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_1116, 5);
lean_dec(x_1119);
lean_ctor_set(x_1116, 5, x_1114);
x_1120 = lean_st_ref_set(x_4, x_1116, x_1117);
x_1121 = lean_ctor_get(x_1120, 1);
lean_inc(x_1121);
lean_dec(x_1120);
x_10 = x_1113;
x_11 = x_1121;
goto block_36;
}
else
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1122 = lean_ctor_get(x_1116, 0);
x_1123 = lean_ctor_get(x_1116, 1);
x_1124 = lean_ctor_get(x_1116, 2);
x_1125 = lean_ctor_get(x_1116, 3);
x_1126 = lean_ctor_get(x_1116, 4);
x_1127 = lean_ctor_get(x_1116, 6);
lean_inc(x_1127);
lean_inc(x_1126);
lean_inc(x_1125);
lean_inc(x_1124);
lean_inc(x_1123);
lean_inc(x_1122);
lean_dec(x_1116);
x_1128 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1128, 0, x_1122);
lean_ctor_set(x_1128, 1, x_1123);
lean_ctor_set(x_1128, 2, x_1124);
lean_ctor_set(x_1128, 3, x_1125);
lean_ctor_set(x_1128, 4, x_1126);
lean_ctor_set(x_1128, 5, x_1114);
lean_ctor_set(x_1128, 6, x_1127);
x_1129 = lean_st_ref_set(x_4, x_1128, x_1117);
x_1130 = lean_ctor_get(x_1129, 1);
lean_inc(x_1130);
lean_dec(x_1129);
x_10 = x_1113;
x_11 = x_1130;
goto block_36;
}
}
else
{
lean_object* x_1131; 
lean_dec(x_2);
lean_dec(x_1);
x_1131 = lean_ctor_get(x_1112, 0);
lean_inc(x_1131);
lean_dec(x_1112);
if (lean_obj_tag(x_1131) == 0)
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; uint8_t x_1137; 
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1131, 1);
lean_inc(x_1133);
lean_dec(x_1131);
x_1134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1134, 0, x_1133);
x_1135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1135, 0, x_1134);
x_1136 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1132, x_1135, x_3, x_4, x_5, x_6, x_7, x_8, x_1106);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1132);
x_1137 = !lean_is_exclusive(x_1136);
if (x_1137 == 0)
{
return x_1136;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1138 = lean_ctor_get(x_1136, 0);
x_1139 = lean_ctor_get(x_1136, 1);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1136);
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
return x_1140;
}
}
else
{
lean_object* x_1141; uint8_t x_1142; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1141 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1106);
x_1142 = !lean_is_exclusive(x_1141);
if (x_1142 == 0)
{
return x_1141;
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1143 = lean_ctor_get(x_1141, 0);
x_1144 = lean_ctor_get(x_1141, 1);
lean_inc(x_1144);
lean_inc(x_1143);
lean_dec(x_1141);
x_1145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1145, 0, x_1143);
lean_ctor_set(x_1145, 1, x_1144);
return x_1145;
}
}
}
}
else
{
lean_object* x_1146; uint8_t x_1147; uint8_t x_1252; 
x_1146 = l_Lean_Syntax_getArg(x_1095, x_139);
lean_inc(x_1146);
x_1252 = l_Lean_Syntax_isOfKind(x_1146, x_934);
if (x_1252 == 0)
{
uint8_t x_1253; 
x_1253 = 0;
x_1147 = x_1253;
goto block_1251;
}
else
{
lean_object* x_1254; lean_object* x_1255; uint8_t x_1256; 
x_1254 = l_Lean_Syntax_getArgs(x_1146);
x_1255 = lean_array_get_size(x_1254);
lean_dec(x_1254);
x_1256 = lean_nat_dec_eq(x_1255, x_87);
lean_dec(x_1255);
x_1147 = x_1256;
goto block_1251;
}
block_1251:
{
if (x_1147 == 0)
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
lean_dec(x_1146);
lean_dec(x_1095);
lean_dec(x_242);
x_1148 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
lean_dec(x_1148);
x_1151 = lean_st_ref_get(x_8, x_1150);
x_1152 = lean_ctor_get(x_1151, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1151, 1);
lean_inc(x_1153);
lean_dec(x_1151);
x_1154 = lean_ctor_get(x_1152, 0);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_st_ref_get(x_4, x_1153);
x_1156 = lean_ctor_get(x_1155, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1155, 1);
lean_inc(x_1157);
lean_dec(x_1155);
x_1158 = lean_ctor_get(x_1156, 5);
lean_inc(x_1158);
lean_dec(x_1156);
x_1159 = lean_ctor_get(x_7, 1);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_7, 2);
lean_inc(x_1160);
x_1161 = lean_environment_main_module(x_1154);
x_1162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1162, 0, x_1161);
lean_ctor_set(x_1162, 1, x_1149);
lean_ctor_set(x_1162, 2, x_1159);
lean_ctor_set(x_1162, 3, x_1160);
lean_inc(x_1);
x_1163 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1162, x_1158);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; uint8_t x_1169; 
x_1164 = lean_ctor_get(x_1163, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1163, 1);
lean_inc(x_1165);
lean_dec(x_1163);
x_1166 = lean_st_ref_take(x_4, x_1157);
x_1167 = lean_ctor_get(x_1166, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1166, 1);
lean_inc(x_1168);
lean_dec(x_1166);
x_1169 = !lean_is_exclusive(x_1167);
if (x_1169 == 0)
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1167, 5);
lean_dec(x_1170);
lean_ctor_set(x_1167, 5, x_1165);
x_1171 = lean_st_ref_set(x_4, x_1167, x_1168);
x_1172 = lean_ctor_get(x_1171, 1);
lean_inc(x_1172);
lean_dec(x_1171);
x_10 = x_1164;
x_11 = x_1172;
goto block_36;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
x_1173 = lean_ctor_get(x_1167, 0);
x_1174 = lean_ctor_get(x_1167, 1);
x_1175 = lean_ctor_get(x_1167, 2);
x_1176 = lean_ctor_get(x_1167, 3);
x_1177 = lean_ctor_get(x_1167, 4);
x_1178 = lean_ctor_get(x_1167, 6);
lean_inc(x_1178);
lean_inc(x_1177);
lean_inc(x_1176);
lean_inc(x_1175);
lean_inc(x_1174);
lean_inc(x_1173);
lean_dec(x_1167);
x_1179 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1179, 0, x_1173);
lean_ctor_set(x_1179, 1, x_1174);
lean_ctor_set(x_1179, 2, x_1175);
lean_ctor_set(x_1179, 3, x_1176);
lean_ctor_set(x_1179, 4, x_1177);
lean_ctor_set(x_1179, 5, x_1165);
lean_ctor_set(x_1179, 6, x_1178);
x_1180 = lean_st_ref_set(x_4, x_1179, x_1168);
x_1181 = lean_ctor_get(x_1180, 1);
lean_inc(x_1181);
lean_dec(x_1180);
x_10 = x_1164;
x_11 = x_1181;
goto block_36;
}
}
else
{
lean_object* x_1182; 
lean_dec(x_2);
lean_dec(x_1);
x_1182 = lean_ctor_get(x_1163, 0);
lean_inc(x_1182);
lean_dec(x_1163);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; uint8_t x_1188; 
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1185 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1185, 0, x_1184);
x_1186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1186, 0, x_1185);
x_1187 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1183, x_1186, x_3, x_4, x_5, x_6, x_7, x_8, x_1157);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1183);
x_1188 = !lean_is_exclusive(x_1187);
if (x_1188 == 0)
{
return x_1187;
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1189 = lean_ctor_get(x_1187, 0);
x_1190 = lean_ctor_get(x_1187, 1);
lean_inc(x_1190);
lean_inc(x_1189);
lean_dec(x_1187);
x_1191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set(x_1191, 1, x_1190);
return x_1191;
}
}
else
{
lean_object* x_1192; uint8_t x_1193; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1192 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1157);
x_1193 = !lean_is_exclusive(x_1192);
if (x_1193 == 0)
{
return x_1192;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1194 = lean_ctor_get(x_1192, 0);
x_1195 = lean_ctor_get(x_1192, 1);
lean_inc(x_1195);
lean_inc(x_1194);
lean_dec(x_1192);
x_1196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1196, 0, x_1194);
lean_ctor_set(x_1196, 1, x_1195);
return x_1196;
}
}
}
}
else
{
lean_object* x_1197; lean_object* x_1198; uint8_t x_1199; 
x_1197 = l_Lean_Syntax_getArg(x_1146, x_139);
lean_dec(x_1146);
x_1198 = l_Lean_identKind___closed__2;
lean_inc(x_1197);
x_1199 = l_Lean_Syntax_isOfKind(x_1197, x_1198);
if (x_1199 == 0)
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
lean_dec(x_1197);
lean_dec(x_1095);
lean_dec(x_242);
x_1200 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec(x_1200);
x_1203 = lean_st_ref_get(x_8, x_1202);
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
x_1205 = lean_ctor_get(x_1203, 1);
lean_inc(x_1205);
lean_dec(x_1203);
x_1206 = lean_ctor_get(x_1204, 0);
lean_inc(x_1206);
lean_dec(x_1204);
x_1207 = lean_st_ref_get(x_4, x_1205);
x_1208 = lean_ctor_get(x_1207, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1207, 1);
lean_inc(x_1209);
lean_dec(x_1207);
x_1210 = lean_ctor_get(x_1208, 5);
lean_inc(x_1210);
lean_dec(x_1208);
x_1211 = lean_ctor_get(x_7, 1);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_7, 2);
lean_inc(x_1212);
x_1213 = lean_environment_main_module(x_1206);
x_1214 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1214, 0, x_1213);
lean_ctor_set(x_1214, 1, x_1201);
lean_ctor_set(x_1214, 2, x_1211);
lean_ctor_set(x_1214, 3, x_1212);
lean_inc(x_1);
x_1215 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1214, x_1210);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; 
x_1216 = lean_ctor_get(x_1215, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1215, 1);
lean_inc(x_1217);
lean_dec(x_1215);
x_1218 = lean_st_ref_take(x_4, x_1209);
x_1219 = lean_ctor_get(x_1218, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1218, 1);
lean_inc(x_1220);
lean_dec(x_1218);
x_1221 = !lean_is_exclusive(x_1219);
if (x_1221 == 0)
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1222 = lean_ctor_get(x_1219, 5);
lean_dec(x_1222);
lean_ctor_set(x_1219, 5, x_1217);
x_1223 = lean_st_ref_set(x_4, x_1219, x_1220);
x_1224 = lean_ctor_get(x_1223, 1);
lean_inc(x_1224);
lean_dec(x_1223);
x_10 = x_1216;
x_11 = x_1224;
goto block_36;
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1225 = lean_ctor_get(x_1219, 0);
x_1226 = lean_ctor_get(x_1219, 1);
x_1227 = lean_ctor_get(x_1219, 2);
x_1228 = lean_ctor_get(x_1219, 3);
x_1229 = lean_ctor_get(x_1219, 4);
x_1230 = lean_ctor_get(x_1219, 6);
lean_inc(x_1230);
lean_inc(x_1229);
lean_inc(x_1228);
lean_inc(x_1227);
lean_inc(x_1226);
lean_inc(x_1225);
lean_dec(x_1219);
x_1231 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1231, 0, x_1225);
lean_ctor_set(x_1231, 1, x_1226);
lean_ctor_set(x_1231, 2, x_1227);
lean_ctor_set(x_1231, 3, x_1228);
lean_ctor_set(x_1231, 4, x_1229);
lean_ctor_set(x_1231, 5, x_1217);
lean_ctor_set(x_1231, 6, x_1230);
x_1232 = lean_st_ref_set(x_4, x_1231, x_1220);
x_1233 = lean_ctor_get(x_1232, 1);
lean_inc(x_1233);
lean_dec(x_1232);
x_10 = x_1216;
x_11 = x_1233;
goto block_36;
}
}
else
{
lean_object* x_1234; 
lean_dec(x_2);
lean_dec(x_1);
x_1234 = lean_ctor_get(x_1215, 0);
lean_inc(x_1234);
lean_dec(x_1215);
if (lean_obj_tag(x_1234) == 0)
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; 
x_1235 = lean_ctor_get(x_1234, 0);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1234, 1);
lean_inc(x_1236);
lean_dec(x_1234);
x_1237 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1237, 0, x_1236);
x_1238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1238, 0, x_1237);
x_1239 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1235, x_1238, x_3, x_4, x_5, x_6, x_7, x_8, x_1209);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1235);
x_1240 = !lean_is_exclusive(x_1239);
if (x_1240 == 0)
{
return x_1239;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1241 = lean_ctor_get(x_1239, 0);
x_1242 = lean_ctor_get(x_1239, 1);
lean_inc(x_1242);
lean_inc(x_1241);
lean_dec(x_1239);
x_1243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1243, 0, x_1241);
lean_ctor_set(x_1243, 1, x_1242);
return x_1243;
}
}
else
{
lean_object* x_1244; uint8_t x_1245; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1244 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1209);
x_1245 = !lean_is_exclusive(x_1244);
if (x_1245 == 0)
{
return x_1244;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1246 = lean_ctor_get(x_1244, 0);
x_1247 = lean_ctor_get(x_1244, 1);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_1244);
x_1248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1248, 0, x_1246);
lean_ctor_set(x_1248, 1, x_1247);
return x_1248;
}
}
}
}
else
{
lean_object* x_1249; lean_object* x_1250; 
x_1249 = l_Lean_Syntax_getArg(x_1095, x_243);
lean_dec(x_1095);
x_1250 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_242, x_1197, x_1249, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1250;
}
}
}
}
}
}
}
}
}
block_1505:
{
if (x_1273 == 0)
{
if (x_1272 == 0)
{
uint8_t x_1274; 
lean_dec(x_993);
x_1274 = 0;
x_994 = x_1274;
goto block_1271;
}
else
{
lean_object* x_1275; lean_object* x_1276; uint8_t x_1277; 
x_1275 = l_Lean_Syntax_getArgs(x_993);
lean_dec(x_993);
x_1276 = lean_array_get_size(x_1275);
lean_dec(x_1275);
x_1277 = lean_nat_dec_eq(x_1276, x_87);
lean_dec(x_1276);
x_994 = x_1277;
goto block_1271;
}
}
else
{
lean_object* x_1278; uint8_t x_1279; uint8_t x_1500; 
lean_dec(x_993);
x_1278 = l_Lean_Syntax_getArg(x_942, x_87);
lean_dec(x_942);
lean_inc(x_1278);
x_1500 = l_Lean_Syntax_isOfKind(x_1278, x_934);
if (x_1500 == 0)
{
uint8_t x_1501; 
x_1501 = 0;
x_1279 = x_1501;
goto block_1499;
}
else
{
lean_object* x_1502; lean_object* x_1503; uint8_t x_1504; 
x_1502 = l_Lean_Syntax_getArgs(x_1278);
x_1503 = lean_array_get_size(x_1502);
lean_dec(x_1502);
x_1504 = lean_nat_dec_eq(x_1503, x_87);
lean_dec(x_1503);
x_1279 = x_1504;
goto block_1499;
}
block_1499:
{
if (x_1279 == 0)
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
lean_dec(x_1278);
lean_dec(x_242);
x_1280 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1280, 1);
lean_inc(x_1282);
lean_dec(x_1280);
x_1283 = lean_st_ref_get(x_8, x_1282);
x_1284 = lean_ctor_get(x_1283, 0);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_1283, 1);
lean_inc(x_1285);
lean_dec(x_1283);
x_1286 = lean_ctor_get(x_1284, 0);
lean_inc(x_1286);
lean_dec(x_1284);
x_1287 = lean_st_ref_get(x_4, x_1285);
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1287, 1);
lean_inc(x_1289);
lean_dec(x_1287);
x_1290 = lean_ctor_get(x_1288, 5);
lean_inc(x_1290);
lean_dec(x_1288);
x_1291 = lean_ctor_get(x_7, 1);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_7, 2);
lean_inc(x_1292);
x_1293 = lean_environment_main_module(x_1286);
x_1294 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1294, 0, x_1293);
lean_ctor_set(x_1294, 1, x_1281);
lean_ctor_set(x_1294, 2, x_1291);
lean_ctor_set(x_1294, 3, x_1292);
lean_inc(x_1);
x_1295 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1294, x_1290);
if (lean_obj_tag(x_1295) == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; uint8_t x_1301; 
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
lean_dec(x_1295);
x_1298 = lean_st_ref_take(x_4, x_1289);
x_1299 = lean_ctor_get(x_1298, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_1298, 1);
lean_inc(x_1300);
lean_dec(x_1298);
x_1301 = !lean_is_exclusive(x_1299);
if (x_1301 == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
x_1302 = lean_ctor_get(x_1299, 5);
lean_dec(x_1302);
lean_ctor_set(x_1299, 5, x_1297);
x_1303 = lean_st_ref_set(x_4, x_1299, x_1300);
x_1304 = lean_ctor_get(x_1303, 1);
lean_inc(x_1304);
lean_dec(x_1303);
x_10 = x_1296;
x_11 = x_1304;
goto block_36;
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; 
x_1305 = lean_ctor_get(x_1299, 0);
x_1306 = lean_ctor_get(x_1299, 1);
x_1307 = lean_ctor_get(x_1299, 2);
x_1308 = lean_ctor_get(x_1299, 3);
x_1309 = lean_ctor_get(x_1299, 4);
x_1310 = lean_ctor_get(x_1299, 6);
lean_inc(x_1310);
lean_inc(x_1309);
lean_inc(x_1308);
lean_inc(x_1307);
lean_inc(x_1306);
lean_inc(x_1305);
lean_dec(x_1299);
x_1311 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1311, 0, x_1305);
lean_ctor_set(x_1311, 1, x_1306);
lean_ctor_set(x_1311, 2, x_1307);
lean_ctor_set(x_1311, 3, x_1308);
lean_ctor_set(x_1311, 4, x_1309);
lean_ctor_set(x_1311, 5, x_1297);
lean_ctor_set(x_1311, 6, x_1310);
x_1312 = lean_st_ref_set(x_4, x_1311, x_1300);
x_1313 = lean_ctor_get(x_1312, 1);
lean_inc(x_1313);
lean_dec(x_1312);
x_10 = x_1296;
x_11 = x_1313;
goto block_36;
}
}
else
{
lean_object* x_1314; 
lean_dec(x_2);
lean_dec(x_1);
x_1314 = lean_ctor_get(x_1295, 0);
lean_inc(x_1314);
lean_dec(x_1295);
if (lean_obj_tag(x_1314) == 0)
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; uint8_t x_1320; 
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1314, 1);
lean_inc(x_1316);
lean_dec(x_1314);
x_1317 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1317, 0, x_1316);
x_1318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1318, 0, x_1317);
x_1319 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1315, x_1318, x_3, x_4, x_5, x_6, x_7, x_8, x_1289);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1315);
x_1320 = !lean_is_exclusive(x_1319);
if (x_1320 == 0)
{
return x_1319;
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
x_1321 = lean_ctor_get(x_1319, 0);
x_1322 = lean_ctor_get(x_1319, 1);
lean_inc(x_1322);
lean_inc(x_1321);
lean_dec(x_1319);
x_1323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1323, 0, x_1321);
lean_ctor_set(x_1323, 1, x_1322);
return x_1323;
}
}
else
{
lean_object* x_1324; uint8_t x_1325; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1324 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1289);
x_1325 = !lean_is_exclusive(x_1324);
if (x_1325 == 0)
{
return x_1324;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
x_1326 = lean_ctor_get(x_1324, 0);
x_1327 = lean_ctor_get(x_1324, 1);
lean_inc(x_1327);
lean_inc(x_1326);
lean_dec(x_1324);
x_1328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1328, 0, x_1326);
lean_ctor_set(x_1328, 1, x_1327);
return x_1328;
}
}
}
}
else
{
lean_object* x_1329; uint8_t x_1330; lean_object* x_1492; uint8_t x_1493; 
x_1329 = l_Lean_Syntax_getArg(x_1278, x_139);
lean_dec(x_1278);
x_1492 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_inc(x_1329);
x_1493 = l_Lean_Syntax_isOfKind(x_1329, x_1492);
if (x_1493 == 0)
{
uint8_t x_1494; 
x_1494 = 0;
x_1330 = x_1494;
goto block_1491;
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; uint8_t x_1498; 
x_1495 = l_Lean_Syntax_getArgs(x_1329);
x_1496 = lean_array_get_size(x_1495);
lean_dec(x_1495);
x_1497 = lean_unsigned_to_nat(3u);
x_1498 = lean_nat_dec_eq(x_1496, x_1497);
lean_dec(x_1496);
x_1330 = x_1498;
goto block_1491;
}
block_1491:
{
if (x_1330 == 0)
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
lean_dec(x_1329);
lean_dec(x_242);
x_1331 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = lean_st_ref_get(x_8, x_1333);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
lean_dec(x_1334);
x_1337 = lean_ctor_get(x_1335, 0);
lean_inc(x_1337);
lean_dec(x_1335);
x_1338 = lean_st_ref_get(x_4, x_1336);
x_1339 = lean_ctor_get(x_1338, 0);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1338, 1);
lean_inc(x_1340);
lean_dec(x_1338);
x_1341 = lean_ctor_get(x_1339, 5);
lean_inc(x_1341);
lean_dec(x_1339);
x_1342 = lean_ctor_get(x_7, 1);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_7, 2);
lean_inc(x_1343);
x_1344 = lean_environment_main_module(x_1337);
x_1345 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1345, 0, x_1344);
lean_ctor_set(x_1345, 1, x_1332);
lean_ctor_set(x_1345, 2, x_1342);
lean_ctor_set(x_1345, 3, x_1343);
lean_inc(x_1);
x_1346 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1345, x_1341);
if (lean_obj_tag(x_1346) == 0)
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; 
x_1347 = lean_ctor_get(x_1346, 0);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1346, 1);
lean_inc(x_1348);
lean_dec(x_1346);
x_1349 = lean_st_ref_take(x_4, x_1340);
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec(x_1349);
x_1352 = !lean_is_exclusive(x_1350);
if (x_1352 == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1353 = lean_ctor_get(x_1350, 5);
lean_dec(x_1353);
lean_ctor_set(x_1350, 5, x_1348);
x_1354 = lean_st_ref_set(x_4, x_1350, x_1351);
x_1355 = lean_ctor_get(x_1354, 1);
lean_inc(x_1355);
lean_dec(x_1354);
x_10 = x_1347;
x_11 = x_1355;
goto block_36;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
x_1356 = lean_ctor_get(x_1350, 0);
x_1357 = lean_ctor_get(x_1350, 1);
x_1358 = lean_ctor_get(x_1350, 2);
x_1359 = lean_ctor_get(x_1350, 3);
x_1360 = lean_ctor_get(x_1350, 4);
x_1361 = lean_ctor_get(x_1350, 6);
lean_inc(x_1361);
lean_inc(x_1360);
lean_inc(x_1359);
lean_inc(x_1358);
lean_inc(x_1357);
lean_inc(x_1356);
lean_dec(x_1350);
x_1362 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1362, 0, x_1356);
lean_ctor_set(x_1362, 1, x_1357);
lean_ctor_set(x_1362, 2, x_1358);
lean_ctor_set(x_1362, 3, x_1359);
lean_ctor_set(x_1362, 4, x_1360);
lean_ctor_set(x_1362, 5, x_1348);
lean_ctor_set(x_1362, 6, x_1361);
x_1363 = lean_st_ref_set(x_4, x_1362, x_1351);
x_1364 = lean_ctor_get(x_1363, 1);
lean_inc(x_1364);
lean_dec(x_1363);
x_10 = x_1347;
x_11 = x_1364;
goto block_36;
}
}
else
{
lean_object* x_1365; 
lean_dec(x_2);
lean_dec(x_1);
x_1365 = lean_ctor_get(x_1346, 0);
lean_inc(x_1365);
lean_dec(x_1346);
if (lean_obj_tag(x_1365) == 0)
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; uint8_t x_1371; 
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
lean_dec(x_1365);
x_1368 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1368, 0, x_1367);
x_1369 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1369, 0, x_1368);
x_1370 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1366, x_1369, x_3, x_4, x_5, x_6, x_7, x_8, x_1340);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1366);
x_1371 = !lean_is_exclusive(x_1370);
if (x_1371 == 0)
{
return x_1370;
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1372 = lean_ctor_get(x_1370, 0);
x_1373 = lean_ctor_get(x_1370, 1);
lean_inc(x_1373);
lean_inc(x_1372);
lean_dec(x_1370);
x_1374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1374, 0, x_1372);
lean_ctor_set(x_1374, 1, x_1373);
return x_1374;
}
}
else
{
lean_object* x_1375; uint8_t x_1376; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1375 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1340);
x_1376 = !lean_is_exclusive(x_1375);
if (x_1376 == 0)
{
return x_1375;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1377 = lean_ctor_get(x_1375, 0);
x_1378 = lean_ctor_get(x_1375, 1);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_1375);
x_1379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
return x_1379;
}
}
}
}
else
{
lean_object* x_1380; uint8_t x_1381; uint8_t x_1486; 
x_1380 = l_Lean_Syntax_getArg(x_1329, x_139);
lean_inc(x_1380);
x_1486 = l_Lean_Syntax_isOfKind(x_1380, x_934);
if (x_1486 == 0)
{
uint8_t x_1487; 
x_1487 = 0;
x_1381 = x_1487;
goto block_1485;
}
else
{
lean_object* x_1488; lean_object* x_1489; uint8_t x_1490; 
x_1488 = l_Lean_Syntax_getArgs(x_1380);
x_1489 = lean_array_get_size(x_1488);
lean_dec(x_1488);
x_1490 = lean_nat_dec_eq(x_1489, x_87);
lean_dec(x_1489);
x_1381 = x_1490;
goto block_1485;
}
block_1485:
{
if (x_1381 == 0)
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
lean_dec(x_1380);
lean_dec(x_1329);
lean_dec(x_242);
x_1382 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
lean_dec(x_1382);
x_1385 = lean_st_ref_get(x_8, x_1384);
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_1385, 1);
lean_inc(x_1387);
lean_dec(x_1385);
x_1388 = lean_ctor_get(x_1386, 0);
lean_inc(x_1388);
lean_dec(x_1386);
x_1389 = lean_st_ref_get(x_4, x_1387);
x_1390 = lean_ctor_get(x_1389, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1389, 1);
lean_inc(x_1391);
lean_dec(x_1389);
x_1392 = lean_ctor_get(x_1390, 5);
lean_inc(x_1392);
lean_dec(x_1390);
x_1393 = lean_ctor_get(x_7, 1);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_7, 2);
lean_inc(x_1394);
x_1395 = lean_environment_main_module(x_1388);
x_1396 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1396, 0, x_1395);
lean_ctor_set(x_1396, 1, x_1383);
lean_ctor_set(x_1396, 2, x_1393);
lean_ctor_set(x_1396, 3, x_1394);
lean_inc(x_1);
x_1397 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1396, x_1392);
if (lean_obj_tag(x_1397) == 0)
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; uint8_t x_1403; 
x_1398 = lean_ctor_get(x_1397, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1397, 1);
lean_inc(x_1399);
lean_dec(x_1397);
x_1400 = lean_st_ref_take(x_4, x_1391);
x_1401 = lean_ctor_get(x_1400, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1400, 1);
lean_inc(x_1402);
lean_dec(x_1400);
x_1403 = !lean_is_exclusive(x_1401);
if (x_1403 == 0)
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1404 = lean_ctor_get(x_1401, 5);
lean_dec(x_1404);
lean_ctor_set(x_1401, 5, x_1399);
x_1405 = lean_st_ref_set(x_4, x_1401, x_1402);
x_1406 = lean_ctor_get(x_1405, 1);
lean_inc(x_1406);
lean_dec(x_1405);
x_10 = x_1398;
x_11 = x_1406;
goto block_36;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1407 = lean_ctor_get(x_1401, 0);
x_1408 = lean_ctor_get(x_1401, 1);
x_1409 = lean_ctor_get(x_1401, 2);
x_1410 = lean_ctor_get(x_1401, 3);
x_1411 = lean_ctor_get(x_1401, 4);
x_1412 = lean_ctor_get(x_1401, 6);
lean_inc(x_1412);
lean_inc(x_1411);
lean_inc(x_1410);
lean_inc(x_1409);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1401);
x_1413 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1413, 0, x_1407);
lean_ctor_set(x_1413, 1, x_1408);
lean_ctor_set(x_1413, 2, x_1409);
lean_ctor_set(x_1413, 3, x_1410);
lean_ctor_set(x_1413, 4, x_1411);
lean_ctor_set(x_1413, 5, x_1399);
lean_ctor_set(x_1413, 6, x_1412);
x_1414 = lean_st_ref_set(x_4, x_1413, x_1402);
x_1415 = lean_ctor_get(x_1414, 1);
lean_inc(x_1415);
lean_dec(x_1414);
x_10 = x_1398;
x_11 = x_1415;
goto block_36;
}
}
else
{
lean_object* x_1416; 
lean_dec(x_2);
lean_dec(x_1);
x_1416 = lean_ctor_get(x_1397, 0);
lean_inc(x_1416);
lean_dec(x_1397);
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
x_1421 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1417, x_1420, x_3, x_4, x_5, x_6, x_7, x_8, x_1391);
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
x_1426 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1391);
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
lean_object* x_1431; lean_object* x_1432; uint8_t x_1433; 
x_1431 = l_Lean_Syntax_getArg(x_1380, x_139);
lean_dec(x_1380);
x_1432 = l_Lean_identKind___closed__2;
lean_inc(x_1431);
x_1433 = l_Lean_Syntax_isOfKind(x_1431, x_1432);
if (x_1433 == 0)
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
lean_dec(x_1431);
lean_dec(x_1329);
lean_dec(x_242);
x_1434 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1434, 1);
lean_inc(x_1436);
lean_dec(x_1434);
x_1437 = lean_st_ref_get(x_8, x_1436);
x_1438 = lean_ctor_get(x_1437, 0);
lean_inc(x_1438);
x_1439 = lean_ctor_get(x_1437, 1);
lean_inc(x_1439);
lean_dec(x_1437);
x_1440 = lean_ctor_get(x_1438, 0);
lean_inc(x_1440);
lean_dec(x_1438);
x_1441 = lean_st_ref_get(x_4, x_1439);
x_1442 = lean_ctor_get(x_1441, 0);
lean_inc(x_1442);
x_1443 = lean_ctor_get(x_1441, 1);
lean_inc(x_1443);
lean_dec(x_1441);
x_1444 = lean_ctor_get(x_1442, 5);
lean_inc(x_1444);
lean_dec(x_1442);
x_1445 = lean_ctor_get(x_7, 1);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_7, 2);
lean_inc(x_1446);
x_1447 = lean_environment_main_module(x_1440);
x_1448 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1448, 0, x_1447);
lean_ctor_set(x_1448, 1, x_1435);
lean_ctor_set(x_1448, 2, x_1445);
lean_ctor_set(x_1448, 3, x_1446);
lean_inc(x_1);
x_1449 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1448, x_1444);
if (lean_obj_tag(x_1449) == 0)
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; uint8_t x_1455; 
x_1450 = lean_ctor_get(x_1449, 0);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1449, 1);
lean_inc(x_1451);
lean_dec(x_1449);
x_1452 = lean_st_ref_take(x_4, x_1443);
x_1453 = lean_ctor_get(x_1452, 0);
lean_inc(x_1453);
x_1454 = lean_ctor_get(x_1452, 1);
lean_inc(x_1454);
lean_dec(x_1452);
x_1455 = !lean_is_exclusive(x_1453);
if (x_1455 == 0)
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1456 = lean_ctor_get(x_1453, 5);
lean_dec(x_1456);
lean_ctor_set(x_1453, 5, x_1451);
x_1457 = lean_st_ref_set(x_4, x_1453, x_1454);
x_1458 = lean_ctor_get(x_1457, 1);
lean_inc(x_1458);
lean_dec(x_1457);
x_10 = x_1450;
x_11 = x_1458;
goto block_36;
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
x_1459 = lean_ctor_get(x_1453, 0);
x_1460 = lean_ctor_get(x_1453, 1);
x_1461 = lean_ctor_get(x_1453, 2);
x_1462 = lean_ctor_get(x_1453, 3);
x_1463 = lean_ctor_get(x_1453, 4);
x_1464 = lean_ctor_get(x_1453, 6);
lean_inc(x_1464);
lean_inc(x_1463);
lean_inc(x_1462);
lean_inc(x_1461);
lean_inc(x_1460);
lean_inc(x_1459);
lean_dec(x_1453);
x_1465 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1465, 0, x_1459);
lean_ctor_set(x_1465, 1, x_1460);
lean_ctor_set(x_1465, 2, x_1461);
lean_ctor_set(x_1465, 3, x_1462);
lean_ctor_set(x_1465, 4, x_1463);
lean_ctor_set(x_1465, 5, x_1451);
lean_ctor_set(x_1465, 6, x_1464);
x_1466 = lean_st_ref_set(x_4, x_1465, x_1454);
x_1467 = lean_ctor_get(x_1466, 1);
lean_inc(x_1467);
lean_dec(x_1466);
x_10 = x_1450;
x_11 = x_1467;
goto block_36;
}
}
else
{
lean_object* x_1468; 
lean_dec(x_2);
lean_dec(x_1);
x_1468 = lean_ctor_get(x_1449, 0);
lean_inc(x_1468);
lean_dec(x_1449);
if (lean_obj_tag(x_1468) == 0)
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; uint8_t x_1474; 
x_1469 = lean_ctor_get(x_1468, 0);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1468, 1);
lean_inc(x_1470);
lean_dec(x_1468);
x_1471 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1471, 0, x_1470);
x_1472 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1472, 0, x_1471);
x_1473 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabTermAux___main___spec__1___rarg(x_1469, x_1472, x_3, x_4, x_5, x_6, x_7, x_8, x_1443);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1469);
x_1474 = !lean_is_exclusive(x_1473);
if (x_1474 == 0)
{
return x_1473;
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; 
x_1475 = lean_ctor_get(x_1473, 0);
x_1476 = lean_ctor_get(x_1473, 1);
lean_inc(x_1476);
lean_inc(x_1475);
lean_dec(x_1473);
x_1477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1477, 0, x_1475);
lean_ctor_set(x_1477, 1, x_1476);
return x_1477;
}
}
else
{
lean_object* x_1478; uint8_t x_1479; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1478 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_20__elabCDot___spec__1___rarg(x_1443);
x_1479 = !lean_is_exclusive(x_1478);
if (x_1479 == 0)
{
return x_1478;
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1480 = lean_ctor_get(x_1478, 0);
x_1481 = lean_ctor_get(x_1478, 1);
lean_inc(x_1481);
lean_inc(x_1480);
lean_dec(x_1478);
x_1482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1482, 0, x_1480);
lean_ctor_set(x_1482, 1, x_1481);
return x_1482;
}
}
}
}
else
{
lean_object* x_1483; lean_object* x_1484; 
x_1483 = l_Lean_Syntax_getArg(x_1329, x_243);
lean_dec(x_1329);
x_1484 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_242, x_1431, x_1483, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_1484;
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
lean_object* l___private_Lean_Elab_Match_42__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
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
x_20 = l___private_Lean_Elab_Match_33__waitExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_27 = l___private_Lean_Elab_Match_32__elabMatchAux(x_24, x_25, x_26, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_24);
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
lean_object* initialize_Lean_Meta_EqnCompiler_MatchPatternAttr(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_Match(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_MatchPatternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15);
l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16 = _init_l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16);
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
l___private_Lean_Elab_Match_15__processVar___closed__1 = _init_l___private_Lean_Elab_Match_15__processVar___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__1);
l___private_Lean_Elab_Match_15__processVar___closed__2 = _init_l___private_Lean_Elab_Match_15__processVar___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__2);
l___private_Lean_Elab_Match_15__processVar___closed__3 = _init_l___private_Lean_Elab_Match_15__processVar___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__3);
l___private_Lean_Elab_Match_15__processVar___closed__4 = _init_l___private_Lean_Elab_Match_15__processVar___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__4);
l___private_Lean_Elab_Match_15__processVar___closed__5 = _init_l___private_Lean_Elab_Match_15__processVar___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__5);
l___private_Lean_Elab_Match_15__processVar___closed__6 = _init_l___private_Lean_Elab_Match_15__processVar___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__6);
l___private_Lean_Elab_Match_15__processVar___closed__7 = _init_l___private_Lean_Elab_Match_15__processVar___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__7);
l___private_Lean_Elab_Match_15__processVar___closed__8 = _init_l___private_Lean_Elab_Match_15__processVar___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__8);
l___private_Lean_Elab_Match_15__processVar___closed__9 = _init_l___private_Lean_Elab_Match_15__processVar___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_15__processVar___closed__9);
l___private_Lean_Elab_Match_16__processIdAux___closed__1 = _init_l___private_Lean_Elab_Match_16__processIdAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___closed__1);
l___private_Lean_Elab_Match_16__processIdAux___closed__2 = _init_l___private_Lean_Elab_Match_16__processIdAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___closed__2);
l___private_Lean_Elab_Match_16__processIdAux___closed__3 = _init_l___private_Lean_Elab_Match_16__processIdAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___closed__3);
l___private_Lean_Elab_Match_16__processIdAux___closed__4 = _init_l___private_Lean_Elab_Match_16__processIdAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___closed__4);
l___private_Lean_Elab_Match_16__processIdAux___closed__5 = _init_l___private_Lean_Elab_Match_16__processIdAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___closed__5);
l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2);
l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3 = _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__4 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__4();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___closed__4);
l___private_Lean_Elab_Match_20__collect___main___closed__1 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__1);
l___private_Lean_Elab_Match_20__collect___main___closed__2 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__2);
l___private_Lean_Elab_Match_20__collect___main___closed__3 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__3);
l___private_Lean_Elab_Match_20__collect___main___closed__4 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__4);
l___private_Lean_Elab_Match_20__collect___main___closed__5 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__5);
l___private_Lean_Elab_Match_20__collect___main___closed__6 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__6);
l___private_Lean_Elab_Match_20__collect___main___closed__7 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__7);
l___private_Lean_Elab_Match_20__collect___main___closed__8 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__8);
l___private_Lean_Elab_Match_20__collect___main___closed__9 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__9);
l___private_Lean_Elab_Match_20__collect___main___closed__10 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__10);
l___private_Lean_Elab_Match_20__collect___main___closed__11 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__11);
l___private_Lean_Elab_Match_20__collect___main___closed__12 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__12);
l___private_Lean_Elab_Match_20__collect___main___closed__13 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__13);
l___private_Lean_Elab_Match_20__collect___main___closed__14 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__14);
l___private_Lean_Elab_Match_20__collect___main___closed__15 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__15);
l___private_Lean_Elab_Match_20__collect___main___closed__16 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__16);
l___private_Lean_Elab_Match_20__collect___main___closed__17 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__17);
l___private_Lean_Elab_Match_20__collect___main___closed__18 = _init_l___private_Lean_Elab_Match_20__collect___main___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___closed__18);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__2);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__4___closed__3);
l___private_Lean_Elab_Match_21__collectPatternVars___closed__1 = _init_l___private_Lean_Elab_Match_21__collectPatternVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_21__collectPatternVars___closed__1);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3);
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
l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2);
l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3 = _init_l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3);
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
l_Lean_Elab_Term_reportElimResultErrors___closed__1 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__1);
l_Lean_Elab_Term_reportElimResultErrors___closed__2 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__2);
l_Lean_Elab_Term_reportElimResultErrors___closed__3 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__3);
l_Lean_Elab_Term_reportElimResultErrors___closed__4 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__4);
l_Lean_Elab_Term_reportElimResultErrors___closed__5 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__5);
l_Lean_Elab_Term_reportElimResultErrors___closed__6 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__6);
l_Lean_Elab_Term_reportElimResultErrors___closed__7 = _init_l_Lean_Elab_Term_reportElimResultErrors___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_reportElimResultErrors___closed__7);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__1 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__1);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__2 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__2);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__3 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__3);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__4 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__4);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__5 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__5);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__6 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__6);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__7 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__7);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__8 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__8);
l___private_Lean_Elab_Match_32__elabMatchAux___closed__9 = _init_l___private_Lean_Elab_Match_32__elabMatchAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_32__elabMatchAux___closed__9);
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1);
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2);
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3);
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4);
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5);
l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1 = _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1);
l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2 = _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2);
l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3 = _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3);
l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4 = _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4);
l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5 = _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5);
l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1 = _init_l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1);
l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1 = _init_l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1);
l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Match_42__regTraceClasses(lean_io_mk_world());
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
