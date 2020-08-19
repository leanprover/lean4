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
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2;
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_Match_2__withAltsAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts(lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__1;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId___boxed(lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__4;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__4;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__8;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_16__processIdAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10;
extern lean_object* l_Lean_Parser_Term_eq___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__9;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__1;
lean_object* l_Lean_Elab_Term_mkMotiveType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__7;
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_23__withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_36__mkOptType(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
lean_object* l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_40__mkNewAlts(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10;
lean_object* l___private_Lean_Elab_Match_15__processVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__3(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_letDecl___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__2;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__9;
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2;
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__6;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9;
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern(lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8;
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__4;
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
extern lean_object* l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_40__mkNewAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__14;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_42__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
lean_object* l_Lean_Elab_Term_reportElimResultErrors(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Term_CollectPatternVars_withRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_nomatch___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns___main___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__1;
lean_object* l___private_Lean_Elab_Match_26__markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_40__mkNewAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(uint8_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern(lean_object*);
extern lean_object* l_Lean_EqnCompiler_matchPatternAttr;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__1;
lean_object* l___private_Lean_Elab_Match_26__markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_33__waitExpectedType(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous(lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__5;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__3;
lean_object* l_Lean_Elab_Term_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__2;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Match_30__getFieldsBinderInfo(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_39__mkNewAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind;
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2;
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
lean_object* l_Lean_Elab_expandMacros___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1;
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__6;
extern lean_object* l_Lean_Options_empty;
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
lean_object* l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__7;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l___private_Lean_Elab_Match_38__mkNewPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__3;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_34__elabMatchCore___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__9;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
lean_object* l___private_Lean_Elab_Match_29__mkLocalDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*);
extern lean_object* l_Lean_Meta_mkEqRefl___closed__2;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__1;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_withRef(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__7;
extern lean_object* l_Lean_Parser_Command_openRenamingItem___elambda__1___closed__5;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_reportElimResultErrors___closed__3;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_BinderInfo_inhabited;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_MessageData_coeOfListExpr___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__5;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__7;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__8;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__3;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_30__getFieldsBinderInfo___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__5;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_40__mkNewAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
lean_object* l_Lean_Elab_Term_mkMotiveType___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_18__processId(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Match_23__withPatternVars(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_setOptionFromString___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___closed__8;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8;
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__2;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_39__mkNewAlt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected(lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVarWithId(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_toString___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__6;
lean_object* l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6;
lean_object* l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5;
extern lean_object* l_Nat_Inhabited;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString(lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__15;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13;
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(uint8_t, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS(lean_object*);
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_41__expandMatchDiscr_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5;
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__5;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_17__processCtor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
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
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_let___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_8 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_Term_getMainModule___rarg(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Array_empty___closed__1;
x_13 = lean_array_push(x_12, x_3);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_15 = lean_array_push(x_13, x_14);
x_16 = lean_array_push(x_15, x_14);
x_17 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_18 = lean_array_push(x_16, x_17);
x_19 = lean_array_push(x_18, x_2);
x_20 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_push(x_12, x_21);
x_23 = l_Lean_Parser_Term_letDecl___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_26 = lean_array_push(x_25, x_24);
x_27 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_array_push(x_28, x_4);
x_30 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_6, 7);
lean_inc(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_6, 7, x_35);
x_36 = 1;
x_37 = l_Lean_Elab_Term_elabTerm(x_31, x_5, x_36, x_6, x_11);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_ctor_get(x_6, 3);
x_42 = lean_ctor_get(x_6, 4);
x_43 = lean_ctor_get(x_6, 5);
x_44 = lean_ctor_get(x_6, 6);
x_45 = lean_ctor_get(x_6, 7);
x_46 = lean_ctor_get(x_6, 8);
x_47 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_50 = lean_ctor_get(x_6, 9);
lean_inc(x_50);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
lean_inc(x_31);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
x_53 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_39);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set(x_53, 5, x_43);
lean_ctor_set(x_53, 6, x_44);
lean_ctor_set(x_53, 7, x_52);
lean_ctor_set(x_53, 8, x_46);
lean_ctor_set(x_53, 9, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*10, x_47);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 1, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 2, x_49);
x_54 = 1;
x_55 = l_Lean_Elab_Term_elabTerm(x_31, x_5, x_54, x_53, x_11);
return x_55;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_9 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Term_getMainModule___rarg(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Array_empty___closed__1;
x_14 = lean_array_push(x_13, x_3);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_16 = lean_array_push(x_14, x_15);
x_17 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
x_18 = lean_array_push(x_17, x_4);
x_19 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_13, x_20);
x_22 = l_Lean_nullKind___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_array_push(x_16, x_23);
x_25 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_array_push(x_26, x_2);
x_28 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_13, x_29);
x_31 = l_Lean_Parser_Term_letDecl___closed__2;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_34 = lean_array_push(x_33, x_32);
x_35 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_array_push(x_36, x_5);
x_38 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_7, 7);
lean_inc(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_7, 7, x_43);
x_44 = 1;
x_45 = l_Lean_Elab_Term_elabTerm(x_39, x_6, x_44, x_7, x_12);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
x_48 = lean_ctor_get(x_7, 2);
x_49 = lean_ctor_get(x_7, 3);
x_50 = lean_ctor_get(x_7, 4);
x_51 = lean_ctor_get(x_7, 5);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
x_54 = lean_ctor_get(x_7, 8);
x_55 = lean_ctor_get_uint8(x_7, sizeof(void*)*10);
x_56 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 1);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 2);
x_58 = lean_ctor_get(x_7, 9);
lean_inc(x_58);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
lean_inc(x_39);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_39);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
x_61 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_49);
lean_ctor_set(x_61, 4, x_50);
lean_ctor_set(x_61, 5, x_51);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_60);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*10, x_55);
lean_ctor_set_uint8(x_61, sizeof(void*)*10 + 1, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*10 + 2, x_57);
x_62 = 1;
x_63 = l_Lean_Elab_Term_elabTerm(x_39, x_6, x_62, x_61, x_12);
return x_63;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_mkHole___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkHole___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_List_format___rarg___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13;
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
x_12 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
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
x_19 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
x_20 = lean_array_push(x_19, x_17);
x_21 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
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
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_3, 9);
lean_inc(x_5);
x_6 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_getEnv___rarg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_environment_main_module(x_11);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
x_19 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_5, x_1, x_2, x_18, x_13);
lean_dec(x_18);
lean_dec(x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set(x_10, 5, x_21);
x_22 = l_Lean_Elab_Term_elabType(x_20, x_3, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
x_28 = lean_ctor_get(x_10, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 4);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_11);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_5, x_1, x_2, x_33, x_28);
lean_dec(x_33);
lean_dec(x_5);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_26);
lean_ctor_set(x_37, 4, x_27);
lean_ctor_set(x_37, 5, x_36);
x_38 = l_Lean_Elab_Term_elabType(x_35, x_3, x_37);
return x_38;
}
}
}
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_5__elabMatchOptType(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
x_2 = l_Lean_Parser_Term_match___elambda__1___closed__1;
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
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_isDefEq(x_4, x_2, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_5);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = l_Lean_indentExpr(x_14);
x_16 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_MessageData_ofList___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = l_Lean_indentExpr(x_22);
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Term_throwError___rarg(x_24, x_6, x_13);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_10, 0);
lean_dec(x_31);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
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
x_38 = lean_array_fget(x_1, x_3);
lean_inc(x_6);
x_39 = l_Lean_Elab_Term_whnf(x_4, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 7)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 2);
lean_inc(x_56);
lean_dec(x_40);
lean_inc(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
lean_inc(x_6);
x_58 = l_Lean_Elab_Term_elabTermEnsuringType(x_38, x_57, x_6, x_41);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_getOptions(x_6, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_65 = l_Lean_checkTraceOption(x_62, x_64);
lean_dec(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_3, x_66);
lean_dec(x_3);
x_68 = lean_expr_instantiate1(x_56, x_59);
lean_dec(x_56);
x_69 = lean_array_push(x_5, x_59);
x_3 = x_67;
x_4 = x_68;
x_5 = x_69;
x_7 = x_63;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_3);
x_71 = l_Nat_repr(x_3);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__16;
x_75 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_59);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_59);
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_55);
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Term_logTrace(x_64, x_83, x_6, x_63);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_3, x_86);
lean_dec(x_3);
x_88 = lean_expr_instantiate1(x_56, x_59);
lean_dec(x_56);
x_89 = lean_array_push(x_5, x_59);
x_3 = x_87;
x_4 = x_88;
x_5 = x_89;
x_7 = x_85;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_58);
if (x_91 == 0)
{
return x_58;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_58, 0);
x_93 = lean_ctor_get(x_58, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_58);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_box(0);
x_42 = x_95;
goto block_54;
}
block_54:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_43 = l_Array_toList___rarg(x_1);
x_44 = l_List_toString___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__1(x_43);
x_45 = l_Array_HasRepr___rarg___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Term_throwError___rarg(x_52, x_6, x_41);
return x_53;
}
}
else
{
uint8_t x_96; 
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_39);
if (x_96 == 0)
{
return x_39;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_39, 0);
x_98 = lean_ctor_get(x_39, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_39);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
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
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_6__elabDiscrsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main(x_1, x_3, x_6, x_2, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_7__elabDiscrs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; uint8_t x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_21 = x_10;
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 2);
x_26 = x_24;
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_11);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_getEnv___rarg(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 4);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_environment_main_module(x_33);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_42);
x_45 = x_27;
x_46 = lean_apply_2(x_45, x_44, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_32, 5);
lean_dec(x_48);
x_49 = lean_ctor_get(x_32, 4);
lean_dec(x_49);
x_50 = lean_ctor_get(x_32, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_32, 2);
lean_dec(x_51);
x_52 = lean_ctor_get(x_32, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_32, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
lean_ctor_set(x_32, 5, x_55);
lean_ctor_set(x_21, 1, x_54);
x_13 = x_21;
x_14 = x_32;
goto block_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_32);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_34);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set(x_58, 4, x_38);
lean_ctor_set(x_58, 5, x_57);
lean_ctor_set(x_21, 1, x_56);
x_13 = x_21;
x_14 = x_58;
goto block_20;
}
}
else
{
lean_object* x_59; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_21);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
lean_dec(x_46);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_Elab_Term_throwErrorAt___rarg(x_60, x_63, x_4, x_32);
lean_dec(x_60);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_4);
x_69 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_32);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
return x_69;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_74 = lean_ctor_get(x_21, 0);
x_75 = lean_ctor_get(x_21, 1);
x_76 = lean_ctor_get(x_21, 2);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_21);
x_77 = x_75;
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_78, 0, x_1);
lean_closure_set(x_78, 1, x_11);
lean_closure_set(x_78, 2, x_77);
x_79 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Elab_Term_getEnv___rarg(x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_4, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 4);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_environment_main_module(x_84);
x_95 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_80);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_93);
x_96 = x_78;
x_97 = lean_apply_2(x_96, x_95, x_90);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 x_98 = x_83;
} else {
 lean_dec_ref(x_83);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 6, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_86);
lean_ctor_set(x_101, 2, x_87);
lean_ctor_set(x_101, 3, x_88);
lean_ctor_set(x_101, 4, x_89);
lean_ctor_set(x_101, 5, x_100);
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_74);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_76);
x_13 = x_102;
x_14 = x_101;
goto block_20;
}
else
{
lean_object* x_103; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
lean_dec(x_97);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_Elab_Term_throwErrorAt___rarg(x_104, x_107, x_4, x_83);
lean_dec(x_104);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_4);
x_113 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_83);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = x_13;
x_18 = lean_array_fset(x_12, x_2, x_17);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_18;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = x_1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2), 5, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_7);
x_10 = x_9;
x_11 = lean_apply_2(x_10, x_2, x_6);
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
x_9 = l_Lean_Parser_Term_matchAlt___closed__2;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_filterAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__1(x_4, x_5, x_5);
x_7 = x_6;
x_8 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__2(x_5, x_7);
x_9 = x_8;
return x_9;
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
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Name_toString___closed__1;
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
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Term_mkFreshId(x_1, x_2);
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
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1);
x_6 = l_Lean_mkMVar(x_5);
x_7 = l_Lean_Elab_Term_mkInaccessible(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabMVarWithIdKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMVarWithIdKind___boxed), 4, 0);
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
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = 1;
x_8 = l_Lean_Elab_Term_elabTerm(x_6, x_2, x_7, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Elab_Term_mkInaccessible(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_Elab_Term_mkInaccessible(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabInaccessible(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabInaccessible___boxed), 4, 0);
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
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3;
x_5 = l_Lean_Elab_Term_throwError___rarg(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_withRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 9);
lean_dec(x_7);
lean_ctor_set(x_4, 9, x_1);
x_8 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_ctor_get(x_4, 6);
x_16 = lean_ctor_get(x_4, 7);
x_17 = lean_ctor_get(x_4, 8);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_11);
lean_ctor_set(x_21, 3, x_12);
lean_ctor_set(x_21, 4, x_13);
lean_ctor_set(x_21, 5, x_14);
lean_ctor_set(x_21, 6, x_15);
lean_ctor_set(x_21, 7, x_16);
lean_ctor_set(x_21, 8, x_17);
lean_ctor_set(x_21, 9, x_1);
lean_ctor_set_uint8(x_21, sizeof(void*)*10, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*10 + 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*10 + 2, x_20);
x_22 = lean_apply_3(x_2, x_3, x_21, x_5);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_withRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_withRef___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
lean_inc(x_5);
x_14 = l_Lean_Meta_getLocalDecl(x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_binderInfo(x_15);
lean_dec(x_15);
x_18 = l_Lean_BinderInfo_isExplicit(x_17);
if (x_18 == 0)
{
x_3 = x_12;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_20;
x_6 = x_16;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_1, x_8, x_8, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
x_11 = l_Lean_Meta_getFVarLocalDecl(x_10, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_14);
x_15 = l_Lean_Meta_isClassQuick___main(x_14, x_4, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_5 = x_17;
goto _start;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_22 = x_15;
} else {
 lean_dec_ref(x_15);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_85; uint8_t x_86; 
x_29 = lean_ctor_get(x_27, 2);
x_85 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_27, 2, x_85);
x_86 = !lean_is_exclusive(x_4);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_4, 2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_23);
lean_ctor_set(x_88, 1, x_10);
x_89 = lean_array_push(x_87, x_88);
lean_ctor_set(x_4, 2, x_89);
x_90 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_25, x_4, x_21);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_91);
x_30 = x_93;
x_31 = x_92;
goto block_84;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_30 = x_96;
x_31 = x_95;
goto block_84;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_4, 0);
x_98 = lean_ctor_get(x_4, 1);
x_99 = lean_ctor_get(x_4, 2);
x_100 = lean_ctor_get(x_4, 3);
x_101 = lean_ctor_get(x_4, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_4);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_23);
lean_ctor_set(x_102, 1, x_10);
x_103 = lean_array_push(x_99, x_102);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
x_105 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_25, x_104, x_21);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_106);
x_30 = x_108;
x_31 = x_107;
goto block_84;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_109);
x_30 = x_111;
x_31 = x_110;
goto block_84;
}
}
block_84:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 2);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 2);
lean_dec(x_37);
lean_ctor_set(x_32, 2, x_29);
if (lean_is_scalar(x_22)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_22;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
x_41 = lean_ctor_get(x_32, 3);
x_42 = lean_ctor_get(x_32, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_31, 2, x_43);
if (lean_is_scalar(x_22)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_22;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
x_47 = lean_ctor_get(x_31, 3);
x_48 = lean_ctor_get(x_31, 4);
x_49 = lean_ctor_get(x_31, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_32, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_32, 4);
lean_inc(x_53);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_54 = x_32;
} else {
 lean_dec_ref(x_32);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_29);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_49);
if (lean_is_scalar(x_22)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_22;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_31, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_30, 0);
lean_inc(x_59);
lean_dec(x_30);
x_60 = !lean_is_exclusive(x_31);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_31, 2);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_58, 2);
lean_dec(x_63);
lean_ctor_set(x_58, 2, x_29);
if (lean_is_scalar(x_22)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_22;
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_31);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
x_67 = lean_ctor_get(x_58, 3);
x_68 = lean_ctor_get(x_58, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_29);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_31, 2, x_69);
if (lean_is_scalar(x_22)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_22;
}
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_31);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_31, 0);
x_72 = lean_ctor_get(x_31, 1);
x_73 = lean_ctor_get(x_31, 3);
x_74 = lean_ctor_get(x_31, 4);
x_75 = lean_ctor_get(x_31, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_31);
x_76 = lean_ctor_get(x_58, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_58, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_58, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 x_80 = x_58;
} else {
 lean_dec_ref(x_58);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_29);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_72);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_73);
lean_ctor_set(x_82, 4, x_74);
lean_ctor_set(x_82, 5, x_75);
if (lean_is_scalar(x_22)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_22;
}
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_112 = lean_ctor_get(x_27, 0);
x_113 = lean_ctor_get(x_27, 1);
x_114 = lean_ctor_get(x_27, 2);
x_115 = lean_ctor_get(x_27, 3);
x_116 = lean_ctor_get(x_27, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_27);
x_152 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_112);
lean_ctor_set(x_153, 1, x_113);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set(x_153, 4, x_116);
lean_ctor_set(x_21, 2, x_153);
x_154 = lean_ctor_get(x_4, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_4, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_4, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_4, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 4);
lean_inc(x_158);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_159 = x_4;
} else {
 lean_dec_ref(x_4);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_23);
lean_ctor_set(x_160, 1, x_10);
x_161 = lean_array_push(x_156, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_154);
lean_ctor_set(x_162, 1, x_155);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_157);
lean_ctor_set(x_162, 4, x_158);
x_163 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_25, x_162, x_21);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_164);
x_117 = x_166;
x_118 = x_165;
goto block_151;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_167);
x_117 = x_169;
x_118 = x_168;
goto block_151;
}
block_151:
{
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 5);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 4);
lean_inc(x_130);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 x_131 = x_119;
} else {
 lean_dec_ref(x_119);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 5, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_114);
lean_ctor_set(x_132, 3, x_129);
lean_ctor_set(x_132, 4, x_130);
if (lean_is_scalar(x_126)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_126;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_122);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_123);
lean_ctor_set(x_133, 4, x_124);
lean_ctor_set(x_133, 5, x_125);
if (lean_is_scalar(x_22)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_22;
 lean_ctor_set_tag(x_134, 1);
}
lean_ctor_set(x_134, 0, x_120);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_135 = lean_ctor_get(x_118, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_118, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_118, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_118, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_118, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 x_142 = x_118;
} else {
 lean_dec_ref(x_118);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 4);
lean_inc(x_146);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 x_147 = x_135;
} else {
 lean_dec_ref(x_135);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_144);
lean_ctor_set(x_148, 2, x_114);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set(x_148, 4, x_146);
if (lean_is_scalar(x_142)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_142;
}
lean_ctor_set(x_149, 0, x_137);
lean_ctor_set(x_149, 1, x_138);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set(x_149, 4, x_140);
lean_ctor_set(x_149, 5, x_141);
if (lean_is_scalar(x_22)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_22;
}
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_170 = lean_ctor_get(x_21, 2);
x_171 = lean_ctor_get(x_21, 0);
x_172 = lean_ctor_get(x_21, 1);
x_173 = lean_ctor_get(x_21, 3);
x_174 = lean_ctor_get(x_21, 4);
x_175 = lean_ctor_get(x_21, 5);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_170);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_21);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_170, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_170, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 4);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
x_217 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_181)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_181;
}
lean_ctor_set(x_218, 0, x_176);
lean_ctor_set(x_218, 1, x_177);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_179);
lean_ctor_set(x_218, 4, x_180);
x_219 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_219, 0, x_171);
lean_ctor_set(x_219, 1, x_172);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_173);
lean_ctor_set(x_219, 4, x_174);
lean_ctor_set(x_219, 5, x_175);
x_220 = lean_ctor_get(x_4, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_4, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_4, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_4, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_4, 4);
lean_inc(x_224);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_225 = x_4;
} else {
 lean_dec_ref(x_4);
 x_225 = lean_box(0);
}
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_23);
lean_ctor_set(x_226, 1, x_10);
x_227 = lean_array_push(x_222, x_226);
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 5, 0);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_220);
lean_ctor_set(x_228, 1, x_221);
lean_ctor_set(x_228, 2, x_227);
lean_ctor_set(x_228, 3, x_223);
lean_ctor_set(x_228, 4, x_224);
x_229 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_25, x_228, x_219);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_230);
x_182 = x_232;
x_183 = x_231;
goto block_216;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_233);
x_182 = x_235;
x_183 = x_234;
goto block_216;
}
block_216:
{
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_184 = lean_ctor_get(x_183, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 5);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_184, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_184, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_184, 4);
lean_inc(x_195);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 x_196 = x_184;
} else {
 lean_dec_ref(x_184);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 5, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set(x_197, 2, x_178);
lean_ctor_set(x_197, 3, x_194);
lean_ctor_set(x_197, 4, x_195);
if (lean_is_scalar(x_191)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_191;
}
lean_ctor_set(x_198, 0, x_186);
lean_ctor_set(x_198, 1, x_187);
lean_ctor_set(x_198, 2, x_197);
lean_ctor_set(x_198, 3, x_188);
lean_ctor_set(x_198, 4, x_189);
lean_ctor_set(x_198, 5, x_190);
if (lean_is_scalar(x_22)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_22;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_200 = lean_ctor_get(x_183, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_182, 0);
lean_inc(x_201);
lean_dec(x_182);
x_202 = lean_ctor_get(x_183, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_183, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_183, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_183, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_183, 5);
lean_inc(x_206);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 x_207 = x_183;
} else {
 lean_dec_ref(x_183);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_200, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 4);
lean_inc(x_211);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 x_212 = x_200;
} else {
 lean_dec_ref(x_200);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_208);
lean_ctor_set(x_213, 1, x_209);
lean_ctor_set(x_213, 2, x_178);
lean_ctor_set(x_213, 3, x_210);
lean_ctor_set(x_213, 4, x_211);
if (lean_is_scalar(x_207)) {
 x_214 = lean_alloc_ctor(0, 6, 0);
} else {
 x_214 = x_207;
}
lean_ctor_set(x_214, 0, x_202);
lean_ctor_set(x_214, 1, x_203);
lean_ctor_set(x_214, 2, x_213);
lean_ctor_set(x_214, 3, x_204);
lean_ctor_set(x_214, 4, x_205);
lean_ctor_set(x_214, 5, x_206);
if (lean_is_scalar(x_22)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_22;
}
lean_ctor_set(x_215, 0, x_201);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
default: 
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_15, 1);
lean_inc(x_236);
lean_dec(x_15);
lean_inc(x_4);
x_237 = l_Lean_Meta_isClassExpensive___main(x_14, x_4, x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_10);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_nat_add(x_3, x_240);
lean_dec(x_3);
x_3 = x_241;
x_5 = x_239;
goto _start;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_244 = x_237;
} else {
 lean_dec_ref(x_237);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_238, 0);
lean_inc(x_245);
lean_dec(x_238);
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_3, x_246);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_243);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_243, 2);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_307; uint8_t x_308; 
x_251 = lean_ctor_get(x_249, 2);
x_307 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_249, 2, x_307);
x_308 = !lean_is_exclusive(x_4);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_4, 2);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_245);
lean_ctor_set(x_310, 1, x_10);
x_311 = lean_array_push(x_309, x_310);
lean_ctor_set(x_4, 2, x_311);
x_312 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_247, x_4, x_243);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_313);
x_252 = x_315;
x_253 = x_314;
goto block_306;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_312, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
lean_dec(x_312);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_252 = x_318;
x_253 = x_317;
goto block_306;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_4, 0);
x_320 = lean_ctor_get(x_4, 1);
x_321 = lean_ctor_get(x_4, 2);
x_322 = lean_ctor_get(x_4, 3);
x_323 = lean_ctor_get(x_4, 4);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_4);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_245);
lean_ctor_set(x_324, 1, x_10);
x_325 = lean_array_push(x_321, x_324);
x_326 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_326, 0, x_319);
lean_ctor_set(x_326, 1, x_320);
lean_ctor_set(x_326, 2, x_325);
lean_ctor_set(x_326, 3, x_322);
lean_ctor_set(x_326, 4, x_323);
x_327 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_247, x_326, x_243);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_252 = x_330;
x_253 = x_329;
goto block_306;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_327, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_327, 1);
lean_inc(x_332);
lean_dec(x_327);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_331);
x_252 = x_333;
x_253 = x_332;
goto block_306;
}
}
block_306:
{
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_ctor_get(x_253, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_dec(x_252);
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_253, 2);
lean_dec(x_257);
x_258 = !lean_is_exclusive(x_254);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_254, 2);
lean_dec(x_259);
lean_ctor_set(x_254, 2, x_251);
if (lean_is_scalar(x_244)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_244;
 lean_ctor_set_tag(x_260, 1);
}
lean_ctor_set(x_260, 0, x_255);
lean_ctor_set(x_260, 1, x_253);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_254, 0);
x_262 = lean_ctor_get(x_254, 1);
x_263 = lean_ctor_get(x_254, 3);
x_264 = lean_ctor_get(x_254, 4);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_254);
x_265 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_262);
lean_ctor_set(x_265, 2, x_251);
lean_ctor_set(x_265, 3, x_263);
lean_ctor_set(x_265, 4, x_264);
lean_ctor_set(x_253, 2, x_265);
if (lean_is_scalar(x_244)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_244;
 lean_ctor_set_tag(x_266, 1);
}
lean_ctor_set(x_266, 0, x_255);
lean_ctor_set(x_266, 1, x_253);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_267 = lean_ctor_get(x_253, 0);
x_268 = lean_ctor_get(x_253, 1);
x_269 = lean_ctor_get(x_253, 3);
x_270 = lean_ctor_get(x_253, 4);
x_271 = lean_ctor_get(x_253, 5);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_253);
x_272 = lean_ctor_get(x_254, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_254, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_254, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_254, 4);
lean_inc(x_275);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 lean_ctor_release(x_254, 3);
 lean_ctor_release(x_254, 4);
 x_276 = x_254;
} else {
 lean_dec_ref(x_254);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 5, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_272);
lean_ctor_set(x_277, 1, x_273);
lean_ctor_set(x_277, 2, x_251);
lean_ctor_set(x_277, 3, x_274);
lean_ctor_set(x_277, 4, x_275);
x_278 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_278, 0, x_267);
lean_ctor_set(x_278, 1, x_268);
lean_ctor_set(x_278, 2, x_277);
lean_ctor_set(x_278, 3, x_269);
lean_ctor_set(x_278, 4, x_270);
lean_ctor_set(x_278, 5, x_271);
if (lean_is_scalar(x_244)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_244;
 lean_ctor_set_tag(x_279, 1);
}
lean_ctor_set(x_279, 0, x_255);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_280 = lean_ctor_get(x_253, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_252, 0);
lean_inc(x_281);
lean_dec(x_252);
x_282 = !lean_is_exclusive(x_253);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_253, 2);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_280);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_280, 2);
lean_dec(x_285);
lean_ctor_set(x_280, 2, x_251);
if (lean_is_scalar(x_244)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_244;
}
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_253);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_280, 0);
x_288 = lean_ctor_get(x_280, 1);
x_289 = lean_ctor_get(x_280, 3);
x_290 = lean_ctor_get(x_280, 4);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_280);
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_288);
lean_ctor_set(x_291, 2, x_251);
lean_ctor_set(x_291, 3, x_289);
lean_ctor_set(x_291, 4, x_290);
lean_ctor_set(x_253, 2, x_291);
if (lean_is_scalar(x_244)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_244;
}
lean_ctor_set(x_292, 0, x_281);
lean_ctor_set(x_292, 1, x_253);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_293 = lean_ctor_get(x_253, 0);
x_294 = lean_ctor_get(x_253, 1);
x_295 = lean_ctor_get(x_253, 3);
x_296 = lean_ctor_get(x_253, 4);
x_297 = lean_ctor_get(x_253, 5);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_253);
x_298 = lean_ctor_get(x_280, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_280, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_280, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_280, 4);
lean_inc(x_301);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 x_302 = x_280;
} else {
 lean_dec_ref(x_280);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_298);
lean_ctor_set(x_303, 1, x_299);
lean_ctor_set(x_303, 2, x_251);
lean_ctor_set(x_303, 3, x_300);
lean_ctor_set(x_303, 4, x_301);
x_304 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_304, 0, x_293);
lean_ctor_set(x_304, 1, x_294);
lean_ctor_set(x_304, 2, x_303);
lean_ctor_set(x_304, 3, x_295);
lean_ctor_set(x_304, 4, x_296);
lean_ctor_set(x_304, 5, x_297);
if (lean_is_scalar(x_244)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_244;
}
lean_ctor_set(x_305, 0, x_281);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_334 = lean_ctor_get(x_249, 0);
x_335 = lean_ctor_get(x_249, 1);
x_336 = lean_ctor_get(x_249, 2);
x_337 = lean_ctor_get(x_249, 3);
x_338 = lean_ctor_get(x_249, 4);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_249);
x_374 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_375 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_375, 0, x_334);
lean_ctor_set(x_375, 1, x_335);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_337);
lean_ctor_set(x_375, 4, x_338);
lean_ctor_set(x_243, 2, x_375);
x_376 = lean_ctor_get(x_4, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_4, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_4, 2);
lean_inc(x_378);
x_379 = lean_ctor_get(x_4, 3);
lean_inc(x_379);
x_380 = lean_ctor_get(x_4, 4);
lean_inc(x_380);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_381 = x_4;
} else {
 lean_dec_ref(x_4);
 x_381 = lean_box(0);
}
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_245);
lean_ctor_set(x_382, 1, x_10);
x_383 = lean_array_push(x_378, x_382);
if (lean_is_scalar(x_381)) {
 x_384 = lean_alloc_ctor(0, 5, 0);
} else {
 x_384 = x_381;
}
lean_ctor_set(x_384, 0, x_376);
lean_ctor_set(x_384, 1, x_377);
lean_ctor_set(x_384, 2, x_383);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set(x_384, 4, x_380);
x_385 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_247, x_384, x_243);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_388, 0, x_386);
x_339 = x_388;
x_340 = x_387;
goto block_373;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
lean_dec(x_385);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_339 = x_391;
x_340 = x_390;
goto block_373;
}
block_373:
{
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_341 = lean_ctor_get(x_340, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 0);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 3);
lean_inc(x_345);
x_346 = lean_ctor_get(x_340, 4);
lean_inc(x_346);
x_347 = lean_ctor_get(x_340, 5);
lean_inc(x_347);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 lean_ctor_release(x_340, 5);
 x_348 = x_340;
} else {
 lean_dec_ref(x_340);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_341, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_341, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_341, 3);
lean_inc(x_351);
x_352 = lean_ctor_get(x_341, 4);
lean_inc(x_352);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 lean_ctor_release(x_341, 4);
 x_353 = x_341;
} else {
 lean_dec_ref(x_341);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 5, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_349);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_336);
lean_ctor_set(x_354, 3, x_351);
lean_ctor_set(x_354, 4, x_352);
if (lean_is_scalar(x_348)) {
 x_355 = lean_alloc_ctor(0, 6, 0);
} else {
 x_355 = x_348;
}
lean_ctor_set(x_355, 0, x_343);
lean_ctor_set(x_355, 1, x_344);
lean_ctor_set(x_355, 2, x_354);
lean_ctor_set(x_355, 3, x_345);
lean_ctor_set(x_355, 4, x_346);
lean_ctor_set(x_355, 5, x_347);
if (lean_is_scalar(x_244)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_244;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_342);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_357 = lean_ctor_get(x_340, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_339, 0);
lean_inc(x_358);
lean_dec(x_339);
x_359 = lean_ctor_get(x_340, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_340, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_340, 3);
lean_inc(x_361);
x_362 = lean_ctor_get(x_340, 4);
lean_inc(x_362);
x_363 = lean_ctor_get(x_340, 5);
lean_inc(x_363);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 lean_ctor_release(x_340, 5);
 x_364 = x_340;
} else {
 lean_dec_ref(x_340);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_357, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_357, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_357, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_357, 4);
lean_inc(x_368);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 x_369 = x_357;
} else {
 lean_dec_ref(x_357);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 5, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_365);
lean_ctor_set(x_370, 1, x_366);
lean_ctor_set(x_370, 2, x_336);
lean_ctor_set(x_370, 3, x_367);
lean_ctor_set(x_370, 4, x_368);
if (lean_is_scalar(x_364)) {
 x_371 = lean_alloc_ctor(0, 6, 0);
} else {
 x_371 = x_364;
}
lean_ctor_set(x_371, 0, x_359);
lean_ctor_set(x_371, 1, x_360);
lean_ctor_set(x_371, 2, x_370);
lean_ctor_set(x_371, 3, x_361);
lean_ctor_set(x_371, 4, x_362);
lean_ctor_set(x_371, 5, x_363);
if (lean_is_scalar(x_244)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_244;
}
lean_ctor_set(x_372, 0, x_358);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_392 = lean_ctor_get(x_243, 2);
x_393 = lean_ctor_get(x_243, 0);
x_394 = lean_ctor_get(x_243, 1);
x_395 = lean_ctor_get(x_243, 3);
x_396 = lean_ctor_get(x_243, 4);
x_397 = lean_ctor_get(x_243, 5);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_392);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_243);
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 3);
lean_inc(x_401);
x_402 = lean_ctor_get(x_392, 4);
lean_inc(x_402);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 x_403 = x_392;
} else {
 lean_dec_ref(x_392);
 x_403 = lean_box(0);
}
x_439 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_403)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_403;
}
lean_ctor_set(x_440, 0, x_398);
lean_ctor_set(x_440, 1, x_399);
lean_ctor_set(x_440, 2, x_439);
lean_ctor_set(x_440, 3, x_401);
lean_ctor_set(x_440, 4, x_402);
x_441 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_441, 0, x_393);
lean_ctor_set(x_441, 1, x_394);
lean_ctor_set(x_441, 2, x_440);
lean_ctor_set(x_441, 3, x_395);
lean_ctor_set(x_441, 4, x_396);
lean_ctor_set(x_441, 5, x_397);
x_442 = lean_ctor_get(x_4, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_4, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_4, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_4, 3);
lean_inc(x_445);
x_446 = lean_ctor_get(x_4, 4);
lean_inc(x_446);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_447 = x_4;
} else {
 lean_dec_ref(x_4);
 x_447 = lean_box(0);
}
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_245);
lean_ctor_set(x_448, 1, x_10);
x_449 = lean_array_push(x_444, x_448);
if (lean_is_scalar(x_447)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_447;
}
lean_ctor_set(x_450, 0, x_442);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_449);
lean_ctor_set(x_450, 3, x_445);
lean_ctor_set(x_450, 4, x_446);
x_451 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_247, x_450, x_441);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_452);
x_404 = x_454;
x_405 = x_453;
goto block_438;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_451, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
lean_dec(x_451);
x_457 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_457, 0, x_455);
x_404 = x_457;
x_405 = x_456;
goto block_438;
}
block_438:
{
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_406 = lean_ctor_get(x_405, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
lean_dec(x_404);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_405, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_405, 4);
lean_inc(x_411);
x_412 = lean_ctor_get(x_405, 5);
lean_inc(x_412);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 lean_ctor_release(x_405, 4);
 lean_ctor_release(x_405, 5);
 x_413 = x_405;
} else {
 lean_dec_ref(x_405);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_406, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_406, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_406, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_406, 4);
lean_inc(x_417);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 lean_ctor_release(x_406, 4);
 x_418 = x_406;
} else {
 lean_dec_ref(x_406);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 5, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_414);
lean_ctor_set(x_419, 1, x_415);
lean_ctor_set(x_419, 2, x_400);
lean_ctor_set(x_419, 3, x_416);
lean_ctor_set(x_419, 4, x_417);
if (lean_is_scalar(x_413)) {
 x_420 = lean_alloc_ctor(0, 6, 0);
} else {
 x_420 = x_413;
}
lean_ctor_set(x_420, 0, x_408);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_419);
lean_ctor_set(x_420, 3, x_410);
lean_ctor_set(x_420, 4, x_411);
lean_ctor_set(x_420, 5, x_412);
if (lean_is_scalar(x_244)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_244;
 lean_ctor_set_tag(x_421, 1);
}
lean_ctor_set(x_421, 0, x_407);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_422 = lean_ctor_get(x_405, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_404, 0);
lean_inc(x_423);
lean_dec(x_404);
x_424 = lean_ctor_get(x_405, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_405, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_405, 3);
lean_inc(x_426);
x_427 = lean_ctor_get(x_405, 4);
lean_inc(x_427);
x_428 = lean_ctor_get(x_405, 5);
lean_inc(x_428);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 lean_ctor_release(x_405, 4);
 lean_ctor_release(x_405, 5);
 x_429 = x_405;
} else {
 lean_dec_ref(x_405);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_422, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_422, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_422, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_422, 4);
lean_inc(x_433);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 lean_ctor_release(x_422, 3);
 lean_ctor_release(x_422, 4);
 x_434 = x_422;
} else {
 lean_dec_ref(x_422);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 5, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_400);
lean_ctor_set(x_435, 3, x_432);
lean_ctor_set(x_435, 4, x_433);
if (lean_is_scalar(x_429)) {
 x_436 = lean_alloc_ctor(0, 6, 0);
} else {
 x_436 = x_429;
}
lean_ctor_set(x_436, 0, x_424);
lean_ctor_set(x_436, 1, x_425);
lean_ctor_set(x_436, 2, x_435);
lean_ctor_set(x_436, 3, x_426);
lean_ctor_set(x_436, 4, x_427);
lean_ctor_set(x_436, 5, x_428);
if (lean_is_scalar(x_244)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_244;
}
lean_ctor_set(x_437, 0, x_423);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_458 = !lean_is_exclusive(x_237);
if (x_458 == 0)
{
return x_237;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_237, 0);
x_460 = lean_ctor_get(x_237, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_237);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_462 = !lean_is_exclusive(x_15);
if (x_462 == 0)
{
return x_15;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_15, 0);
x_464 = lean_ctor_get(x_15, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_15);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_466 = !lean_is_exclusive(x_11);
if (x_466 == 0)
{
return x_11;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_11, 0);
x_468 = lean_ctor_get(x_11, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_11);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isForall(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_1, x_10, x_10, x_7, x_8);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(x_2, x_3, x_4, x_1, x_5, x_6, x_7, x_8);
return x_12;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_expr_instantiate_rev_range(x_6, x_5, x_7, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1___boxed), 8, 5);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_7);
x_16 = lean_array_get_size(x_8);
x_17 = lean_nat_dec_lt(x_9, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_13, x_15, x_10, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_13);
x_19 = lean_array_fget(x_8, x_9);
lean_inc(x_10);
x_20 = l_Lean_Meta_getFVarLocalDecl(x_19, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_type(x_21);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_23);
x_24 = l_Lean_Meta_isClassQuick___main(x_23, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_19);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_9, x_27);
lean_dec(x_9);
x_9 = x_28;
x_11 = x_26;
goto _start;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_9, x_33);
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_30, 2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_94; uint8_t x_95; 
x_38 = lean_ctor_get(x_36, 2);
x_94 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_36, 2, x_94);
x_95 = !lean_is_exclusive(x_10);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_10, 2);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_32);
lean_ctor_set(x_97, 1, x_19);
x_98 = lean_array_push(x_96, x_97);
lean_ctor_set(x_10, 2, x_98);
x_99 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34, x_10, x_30);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_100);
x_39 = x_102;
x_40 = x_101;
goto block_93;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_103);
x_39 = x_105;
x_40 = x_104;
goto block_93;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_10, 0);
x_107 = lean_ctor_get(x_10, 1);
x_108 = lean_ctor_get(x_10, 2);
x_109 = lean_ctor_get(x_10, 3);
x_110 = lean_ctor_get(x_10, 4);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_10);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_32);
lean_ctor_set(x_111, 1, x_19);
x_112 = lean_array_push(x_108, x_111);
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_107);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_109);
lean_ctor_set(x_113, 4, x_110);
x_114 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34, x_113, x_30);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_115);
x_39 = x_117;
x_40 = x_116;
goto block_93;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_dec(x_114);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_118);
x_39 = x_120;
x_40 = x_119;
goto block_93;
}
}
block_93:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 2);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 2);
lean_dec(x_46);
lean_ctor_set(x_41, 2, x_38);
if (lean_is_scalar(x_31)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_31;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 3);
x_51 = lean_ctor_get(x_41, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_38);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_40, 2, x_52);
if (lean_is_scalar(x_31)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_31;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_40);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
x_56 = lean_ctor_get(x_40, 3);
x_57 = lean_ctor_get(x_40, 4);
x_58 = lean_ctor_get(x_40, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_59 = lean_ctor_get(x_41, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_41, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_41, 4);
lean_inc(x_62);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 x_63 = x_41;
} else {
 lean_dec_ref(x_41);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_38);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_55);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_56);
lean_ctor_set(x_65, 4, x_57);
lean_ctor_set(x_65, 5, x_58);
if (lean_is_scalar(x_31)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_31;
 lean_ctor_set_tag(x_66, 1);
}
lean_ctor_set(x_66, 0, x_42);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_40, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
lean_dec(x_39);
x_69 = !lean_is_exclusive(x_40);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_40, 2);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_67, 2);
lean_dec(x_72);
lean_ctor_set(x_67, 2, x_38);
if (lean_is_scalar(x_31)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_31;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_40);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
x_76 = lean_ctor_get(x_67, 3);
x_77 = lean_ctor_get(x_67, 4);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_38);
lean_ctor_set(x_78, 3, x_76);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_40, 2, x_78);
if (lean_is_scalar(x_31)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_31;
}
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_40);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_40, 0);
x_81 = lean_ctor_get(x_40, 1);
x_82 = lean_ctor_get(x_40, 3);
x_83 = lean_ctor_get(x_40, 4);
x_84 = lean_ctor_get(x_40, 5);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_40);
x_85 = lean_ctor_get(x_67, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_67, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_67, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_67, 4);
lean_inc(x_88);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 x_89 = x_67;
} else {
 lean_dec_ref(x_67);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_38);
lean_ctor_set(x_90, 3, x_87);
lean_ctor_set(x_90, 4, x_88);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_82);
lean_ctor_set(x_91, 4, x_83);
lean_ctor_set(x_91, 5, x_84);
if (lean_is_scalar(x_31)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_31;
}
lean_ctor_set(x_92, 0, x_68);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_121 = lean_ctor_get(x_36, 0);
x_122 = lean_ctor_get(x_36, 1);
x_123 = lean_ctor_get(x_36, 2);
x_124 = lean_ctor_get(x_36, 3);
x_125 = lean_ctor_get(x_36, 4);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_36);
x_161 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_121);
lean_ctor_set(x_162, 1, x_122);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_124);
lean_ctor_set(x_162, 4, x_125);
lean_ctor_set(x_30, 2, x_162);
x_163 = lean_ctor_get(x_10, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_10, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_10, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_10, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_10, 4);
lean_inc(x_167);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_168 = x_10;
} else {
 lean_dec_ref(x_10);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_32);
lean_ctor_set(x_169, 1, x_19);
x_170 = lean_array_push(x_165, x_169);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 5, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_163);
lean_ctor_set(x_171, 1, x_164);
lean_ctor_set(x_171, 2, x_170);
lean_ctor_set(x_171, 3, x_166);
lean_ctor_set(x_171, 4, x_167);
x_172 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34, x_171, x_30);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_173);
x_126 = x_175;
x_127 = x_174;
goto block_160;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
lean_dec(x_172);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_176);
x_126 = x_178;
x_127 = x_177;
goto block_160;
}
block_160:
{
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 5);
lean_inc(x_134);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_135 = x_127;
} else {
 lean_dec_ref(x_127);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_128, 4);
lean_inc(x_139);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 x_140 = x_128;
} else {
 lean_dec_ref(x_128);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 5, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_141, 1, x_137);
lean_ctor_set(x_141, 2, x_123);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set(x_141, 4, x_139);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 6, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_130);
lean_ctor_set(x_142, 1, x_131);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_142, 3, x_132);
lean_ctor_set(x_142, 4, x_133);
lean_ctor_set(x_142, 5, x_134);
if (lean_is_scalar(x_31)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_31;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_144 = lean_ctor_get(x_127, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
lean_dec(x_126);
x_146 = lean_ctor_get(x_127, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_127, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_127, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_127, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_127, 5);
lean_inc(x_150);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_151 = x_127;
} else {
 lean_dec_ref(x_127);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_144, 4);
lean_inc(x_155);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 lean_ctor_release(x_144, 4);
 x_156 = x_144;
} else {
 lean_dec_ref(x_144);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_153);
lean_ctor_set(x_157, 2, x_123);
lean_ctor_set(x_157, 3, x_154);
lean_ctor_set(x_157, 4, x_155);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(0, 6, 0);
} else {
 x_158 = x_151;
}
lean_ctor_set(x_158, 0, x_146);
lean_ctor_set(x_158, 1, x_147);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_148);
lean_ctor_set(x_158, 4, x_149);
lean_ctor_set(x_158, 5, x_150);
if (lean_is_scalar(x_31)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_31;
}
lean_ctor_set(x_159, 0, x_145);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_179 = lean_ctor_get(x_30, 2);
x_180 = lean_ctor_get(x_30, 0);
x_181 = lean_ctor_get(x_30, 1);
x_182 = lean_ctor_get(x_30, 3);
x_183 = lean_ctor_get(x_30, 4);
x_184 = lean_ctor_get(x_30, 5);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_179);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_30);
x_185 = lean_ctor_get(x_179, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_179, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_179, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_179, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_179, 4);
lean_inc(x_189);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_190 = x_179;
} else {
 lean_dec_ref(x_179);
 x_190 = lean_box(0);
}
x_226 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_190)) {
 x_227 = lean_alloc_ctor(0, 5, 0);
} else {
 x_227 = x_190;
}
lean_ctor_set(x_227, 0, x_185);
lean_ctor_set(x_227, 1, x_186);
lean_ctor_set(x_227, 2, x_226);
lean_ctor_set(x_227, 3, x_188);
lean_ctor_set(x_227, 4, x_189);
x_228 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_228, 0, x_180);
lean_ctor_set(x_228, 1, x_181);
lean_ctor_set(x_228, 2, x_227);
lean_ctor_set(x_228, 3, x_182);
lean_ctor_set(x_228, 4, x_183);
lean_ctor_set(x_228, 5, x_184);
x_229 = lean_ctor_get(x_10, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_10, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_10, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_10, 3);
lean_inc(x_232);
x_233 = lean_ctor_get(x_10, 4);
lean_inc(x_233);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_234 = x_10;
} else {
 lean_dec_ref(x_10);
 x_234 = lean_box(0);
}
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_32);
lean_ctor_set(x_235, 1, x_19);
x_236 = lean_array_push(x_231, x_235);
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(0, 5, 0);
} else {
 x_237 = x_234;
}
lean_ctor_set(x_237, 0, x_229);
lean_ctor_set(x_237, 1, x_230);
lean_ctor_set(x_237, 2, x_236);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set(x_237, 4, x_233);
x_238 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34, x_237, x_228);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_239);
x_191 = x_241;
x_192 = x_240;
goto block_225;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_238, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_238, 1);
lean_inc(x_243);
lean_dec(x_238);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_242);
x_191 = x_244;
x_192 = x_243;
goto block_225;
}
block_225:
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_193 = lean_ctor_get(x_192, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_192, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_200 = x_192;
} else {
 lean_dec_ref(x_192);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 4);
lean_inc(x_204);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 x_205 = x_193;
} else {
 lean_dec_ref(x_193);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 5, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_202);
lean_ctor_set(x_206, 2, x_187);
lean_ctor_set(x_206, 3, x_203);
lean_ctor_set(x_206, 4, x_204);
if (lean_is_scalar(x_200)) {
 x_207 = lean_alloc_ctor(0, 6, 0);
} else {
 x_207 = x_200;
}
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_196);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_197);
lean_ctor_set(x_207, 4, x_198);
lean_ctor_set(x_207, 5, x_199);
if (lean_is_scalar(x_31)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_31;
 lean_ctor_set_tag(x_208, 1);
}
lean_ctor_set(x_208, 0, x_194);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_209 = lean_ctor_get(x_192, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_191, 0);
lean_inc(x_210);
lean_dec(x_191);
x_211 = lean_ctor_get(x_192, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_192, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_192, 3);
lean_inc(x_213);
x_214 = lean_ctor_get(x_192, 4);
lean_inc(x_214);
x_215 = lean_ctor_get(x_192, 5);
lean_inc(x_215);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_216 = x_192;
} else {
 lean_dec_ref(x_192);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_209, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_209, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_209, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_209, 4);
lean_inc(x_220);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 lean_ctor_release(x_209, 4);
 x_221 = x_209;
} else {
 lean_dec_ref(x_209);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 5, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_217);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_187);
lean_ctor_set(x_222, 3, x_219);
lean_ctor_set(x_222, 4, x_220);
if (lean_is_scalar(x_216)) {
 x_223 = lean_alloc_ctor(0, 6, 0);
} else {
 x_223 = x_216;
}
lean_ctor_set(x_223, 0, x_211);
lean_ctor_set(x_223, 1, x_212);
lean_ctor_set(x_223, 2, x_222);
lean_ctor_set(x_223, 3, x_213);
lean_ctor_set(x_223, 4, x_214);
lean_ctor_set(x_223, 5, x_215);
if (lean_is_scalar(x_31)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_31;
}
lean_ctor_set(x_224, 0, x_210);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
default: 
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_24, 1);
lean_inc(x_245);
lean_dec(x_24);
lean_inc(x_10);
x_246 = l_Lean_Meta_isClassExpensive___main(x_23, x_10, x_245);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_19);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_nat_add(x_9, x_249);
lean_dec(x_9);
x_9 = x_250;
x_11 = x_248;
goto _start;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_253 = x_246;
} else {
 lean_dec_ref(x_246);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_247, 0);
lean_inc(x_254);
lean_dec(x_247);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_add(x_9, x_255);
lean_dec(x_9);
x_257 = !lean_is_exclusive(x_252);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_252, 2);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_316; uint8_t x_317; 
x_260 = lean_ctor_get(x_258, 2);
x_316 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_258, 2, x_316);
x_317 = !lean_is_exclusive(x_10);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_10, 2);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_254);
lean_ctor_set(x_319, 1, x_19);
x_320 = lean_array_push(x_318, x_319);
lean_ctor_set(x_10, 2, x_320);
x_321 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_256, x_10, x_252);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_322);
x_261 = x_324;
x_262 = x_323;
goto block_315;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_321, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_321, 1);
lean_inc(x_326);
lean_dec(x_321);
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_325);
x_261 = x_327;
x_262 = x_326;
goto block_315;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_328 = lean_ctor_get(x_10, 0);
x_329 = lean_ctor_get(x_10, 1);
x_330 = lean_ctor_get(x_10, 2);
x_331 = lean_ctor_get(x_10, 3);
x_332 = lean_ctor_get(x_10, 4);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_10);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_254);
lean_ctor_set(x_333, 1, x_19);
x_334 = lean_array_push(x_330, x_333);
x_335 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_335, 0, x_328);
lean_ctor_set(x_335, 1, x_329);
lean_ctor_set(x_335, 2, x_334);
lean_ctor_set(x_335, 3, x_331);
lean_ctor_set(x_335, 4, x_332);
x_336 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_256, x_335, x_252);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_337);
x_261 = x_339;
x_262 = x_338;
goto block_315;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_336, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_336, 1);
lean_inc(x_341);
lean_dec(x_336);
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_340);
x_261 = x_342;
x_262 = x_341;
goto block_315;
}
}
block_315:
{
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_262, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 0);
lean_inc(x_264);
lean_dec(x_261);
x_265 = !lean_is_exclusive(x_262);
if (x_265 == 0)
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_262, 2);
lean_dec(x_266);
x_267 = !lean_is_exclusive(x_263);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_263, 2);
lean_dec(x_268);
lean_ctor_set(x_263, 2, x_260);
if (lean_is_scalar(x_253)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_253;
 lean_ctor_set_tag(x_269, 1);
}
lean_ctor_set(x_269, 0, x_264);
lean_ctor_set(x_269, 1, x_262);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_270 = lean_ctor_get(x_263, 0);
x_271 = lean_ctor_get(x_263, 1);
x_272 = lean_ctor_get(x_263, 3);
x_273 = lean_ctor_get(x_263, 4);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_263);
x_274 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_274, 0, x_270);
lean_ctor_set(x_274, 1, x_271);
lean_ctor_set(x_274, 2, x_260);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set(x_274, 4, x_273);
lean_ctor_set(x_262, 2, x_274);
if (lean_is_scalar(x_253)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_253;
 lean_ctor_set_tag(x_275, 1);
}
lean_ctor_set(x_275, 0, x_264);
lean_ctor_set(x_275, 1, x_262);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_276 = lean_ctor_get(x_262, 0);
x_277 = lean_ctor_get(x_262, 1);
x_278 = lean_ctor_get(x_262, 3);
x_279 = lean_ctor_get(x_262, 4);
x_280 = lean_ctor_get(x_262, 5);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_262);
x_281 = lean_ctor_get(x_263, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_263, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_263, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_263, 4);
lean_inc(x_284);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 lean_ctor_release(x_263, 3);
 lean_ctor_release(x_263, 4);
 x_285 = x_263;
} else {
 lean_dec_ref(x_263);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 5, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_282);
lean_ctor_set(x_286, 2, x_260);
lean_ctor_set(x_286, 3, x_283);
lean_ctor_set(x_286, 4, x_284);
x_287 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_277);
lean_ctor_set(x_287, 2, x_286);
lean_ctor_set(x_287, 3, x_278);
lean_ctor_set(x_287, 4, x_279);
lean_ctor_set(x_287, 5, x_280);
if (lean_is_scalar(x_253)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_253;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_264);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_289 = lean_ctor_get(x_262, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_261, 0);
lean_inc(x_290);
lean_dec(x_261);
x_291 = !lean_is_exclusive(x_262);
if (x_291 == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_262, 2);
lean_dec(x_292);
x_293 = !lean_is_exclusive(x_289);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_289, 2);
lean_dec(x_294);
lean_ctor_set(x_289, 2, x_260);
if (lean_is_scalar(x_253)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_253;
}
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_262);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_289, 0);
x_297 = lean_ctor_get(x_289, 1);
x_298 = lean_ctor_get(x_289, 3);
x_299 = lean_ctor_get(x_289, 4);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_289);
x_300 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_297);
lean_ctor_set(x_300, 2, x_260);
lean_ctor_set(x_300, 3, x_298);
lean_ctor_set(x_300, 4, x_299);
lean_ctor_set(x_262, 2, x_300);
if (lean_is_scalar(x_253)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_253;
}
lean_ctor_set(x_301, 0, x_290);
lean_ctor_set(x_301, 1, x_262);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_302 = lean_ctor_get(x_262, 0);
x_303 = lean_ctor_get(x_262, 1);
x_304 = lean_ctor_get(x_262, 3);
x_305 = lean_ctor_get(x_262, 4);
x_306 = lean_ctor_get(x_262, 5);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_262);
x_307 = lean_ctor_get(x_289, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_289, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_289, 3);
lean_inc(x_309);
x_310 = lean_ctor_get(x_289, 4);
lean_inc(x_310);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 lean_ctor_release(x_289, 2);
 lean_ctor_release(x_289, 3);
 lean_ctor_release(x_289, 4);
 x_311 = x_289;
} else {
 lean_dec_ref(x_289);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(0, 5, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_260);
lean_ctor_set(x_312, 3, x_309);
lean_ctor_set(x_312, 4, x_310);
x_313 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_313, 0, x_302);
lean_ctor_set(x_313, 1, x_303);
lean_ctor_set(x_313, 2, x_312);
lean_ctor_set(x_313, 3, x_304);
lean_ctor_set(x_313, 4, x_305);
lean_ctor_set(x_313, 5, x_306);
if (lean_is_scalar(x_253)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_253;
}
lean_ctor_set(x_314, 0, x_290);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_343 = lean_ctor_get(x_258, 0);
x_344 = lean_ctor_get(x_258, 1);
x_345 = lean_ctor_get(x_258, 2);
x_346 = lean_ctor_get(x_258, 3);
x_347 = lean_ctor_get(x_258, 4);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_258);
x_383 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_384 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_384, 0, x_343);
lean_ctor_set(x_384, 1, x_344);
lean_ctor_set(x_384, 2, x_383);
lean_ctor_set(x_384, 3, x_346);
lean_ctor_set(x_384, 4, x_347);
lean_ctor_set(x_252, 2, x_384);
x_385 = lean_ctor_get(x_10, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_10, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_10, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_10, 3);
lean_inc(x_388);
x_389 = lean_ctor_get(x_10, 4);
lean_inc(x_389);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_390 = x_10;
} else {
 lean_dec_ref(x_10);
 x_390 = lean_box(0);
}
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_254);
lean_ctor_set(x_391, 1, x_19);
x_392 = lean_array_push(x_387, x_391);
if (lean_is_scalar(x_390)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_390;
}
lean_ctor_set(x_393, 0, x_385);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_392);
lean_ctor_set(x_393, 3, x_388);
lean_ctor_set(x_393, 4, x_389);
x_394 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_256, x_393, x_252);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_395);
x_348 = x_397;
x_349 = x_396;
goto block_382;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_394, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_394, 1);
lean_inc(x_399);
lean_dec(x_394);
x_400 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_400, 0, x_398);
x_348 = x_400;
x_349 = x_399;
goto block_382;
}
block_382:
{
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_350 = lean_ctor_get(x_349, 2);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 0);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_349, 4);
lean_inc(x_355);
x_356 = lean_ctor_get(x_349, 5);
lean_inc(x_356);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 lean_ctor_release(x_349, 5);
 x_357 = x_349;
} else {
 lean_dec_ref(x_349);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_350, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_350, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_350, 3);
lean_inc(x_360);
x_361 = lean_ctor_get(x_350, 4);
lean_inc(x_361);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 lean_ctor_release(x_350, 4);
 x_362 = x_350;
} else {
 lean_dec_ref(x_350);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 5, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_358);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set(x_363, 2, x_345);
lean_ctor_set(x_363, 3, x_360);
lean_ctor_set(x_363, 4, x_361);
if (lean_is_scalar(x_357)) {
 x_364 = lean_alloc_ctor(0, 6, 0);
} else {
 x_364 = x_357;
}
lean_ctor_set(x_364, 0, x_352);
lean_ctor_set(x_364, 1, x_353);
lean_ctor_set(x_364, 2, x_363);
lean_ctor_set(x_364, 3, x_354);
lean_ctor_set(x_364, 4, x_355);
lean_ctor_set(x_364, 5, x_356);
if (lean_is_scalar(x_253)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_253;
 lean_ctor_set_tag(x_365, 1);
}
lean_ctor_set(x_365, 0, x_351);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_366 = lean_ctor_get(x_349, 2);
lean_inc(x_366);
x_367 = lean_ctor_get(x_348, 0);
lean_inc(x_367);
lean_dec(x_348);
x_368 = lean_ctor_get(x_349, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_349, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_349, 3);
lean_inc(x_370);
x_371 = lean_ctor_get(x_349, 4);
lean_inc(x_371);
x_372 = lean_ctor_get(x_349, 5);
lean_inc(x_372);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 lean_ctor_release(x_349, 5);
 x_373 = x_349;
} else {
 lean_dec_ref(x_349);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_366, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_366, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_366, 3);
lean_inc(x_376);
x_377 = lean_ctor_get(x_366, 4);
lean_inc(x_377);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 lean_ctor_release(x_366, 2);
 lean_ctor_release(x_366, 3);
 lean_ctor_release(x_366, 4);
 x_378 = x_366;
} else {
 lean_dec_ref(x_366);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 5, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_374);
lean_ctor_set(x_379, 1, x_375);
lean_ctor_set(x_379, 2, x_345);
lean_ctor_set(x_379, 3, x_376);
lean_ctor_set(x_379, 4, x_377);
if (lean_is_scalar(x_373)) {
 x_380 = lean_alloc_ctor(0, 6, 0);
} else {
 x_380 = x_373;
}
lean_ctor_set(x_380, 0, x_368);
lean_ctor_set(x_380, 1, x_369);
lean_ctor_set(x_380, 2, x_379);
lean_ctor_set(x_380, 3, x_370);
lean_ctor_set(x_380, 4, x_371);
lean_ctor_set(x_380, 5, x_372);
if (lean_is_scalar(x_253)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_253;
}
lean_ctor_set(x_381, 0, x_367);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_401 = lean_ctor_get(x_252, 2);
x_402 = lean_ctor_get(x_252, 0);
x_403 = lean_ctor_get(x_252, 1);
x_404 = lean_ctor_get(x_252, 3);
x_405 = lean_ctor_get(x_252, 4);
x_406 = lean_ctor_get(x_252, 5);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_401);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_252);
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_401, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_401, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_401, 4);
lean_inc(x_411);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 lean_ctor_release(x_401, 3);
 lean_ctor_release(x_401, 4);
 x_412 = x_401;
} else {
 lean_dec_ref(x_401);
 x_412 = lean_box(0);
}
x_448 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_412)) {
 x_449 = lean_alloc_ctor(0, 5, 0);
} else {
 x_449 = x_412;
}
lean_ctor_set(x_449, 0, x_407);
lean_ctor_set(x_449, 1, x_408);
lean_ctor_set(x_449, 2, x_448);
lean_ctor_set(x_449, 3, x_410);
lean_ctor_set(x_449, 4, x_411);
x_450 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_450, 0, x_402);
lean_ctor_set(x_450, 1, x_403);
lean_ctor_set(x_450, 2, x_449);
lean_ctor_set(x_450, 3, x_404);
lean_ctor_set(x_450, 4, x_405);
lean_ctor_set(x_450, 5, x_406);
x_451 = lean_ctor_get(x_10, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_10, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_10, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_10, 3);
lean_inc(x_454);
x_455 = lean_ctor_get(x_10, 4);
lean_inc(x_455);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_456 = x_10;
} else {
 lean_dec_ref(x_10);
 x_456 = lean_box(0);
}
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_254);
lean_ctor_set(x_457, 1, x_19);
x_458 = lean_array_push(x_453, x_457);
if (lean_is_scalar(x_456)) {
 x_459 = lean_alloc_ctor(0, 5, 0);
} else {
 x_459 = x_456;
}
lean_ctor_set(x_459, 0, x_451);
lean_ctor_set(x_459, 1, x_452);
lean_ctor_set(x_459, 2, x_458);
lean_ctor_set(x_459, 3, x_454);
lean_ctor_set(x_459, 4, x_455);
x_460 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_256, x_459, x_450);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_461);
x_413 = x_463;
x_414 = x_462;
goto block_447;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_460, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_460, 1);
lean_inc(x_465);
lean_dec(x_460);
x_466 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_466, 0, x_464);
x_413 = x_466;
x_414 = x_465;
goto block_447;
}
block_447:
{
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_415 = lean_ctor_get(x_414, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_413, 0);
lean_inc(x_416);
lean_dec(x_413);
x_417 = lean_ctor_get(x_414, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_414, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 3);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 4);
lean_inc(x_420);
x_421 = lean_ctor_get(x_414, 5);
lean_inc(x_421);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 lean_ctor_release(x_414, 4);
 lean_ctor_release(x_414, 5);
 x_422 = x_414;
} else {
 lean_dec_ref(x_414);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_415, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_415, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_415, 3);
lean_inc(x_425);
x_426 = lean_ctor_get(x_415, 4);
lean_inc(x_426);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 lean_ctor_release(x_415, 4);
 x_427 = x_415;
} else {
 lean_dec_ref(x_415);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(0, 5, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_423);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_409);
lean_ctor_set(x_428, 3, x_425);
lean_ctor_set(x_428, 4, x_426);
if (lean_is_scalar(x_422)) {
 x_429 = lean_alloc_ctor(0, 6, 0);
} else {
 x_429 = x_422;
}
lean_ctor_set(x_429, 0, x_417);
lean_ctor_set(x_429, 1, x_418);
lean_ctor_set(x_429, 2, x_428);
lean_ctor_set(x_429, 3, x_419);
lean_ctor_set(x_429, 4, x_420);
lean_ctor_set(x_429, 5, x_421);
if (lean_is_scalar(x_253)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_253;
 lean_ctor_set_tag(x_430, 1);
}
lean_ctor_set(x_430, 0, x_416);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_431 = lean_ctor_get(x_414, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_413, 0);
lean_inc(x_432);
lean_dec(x_413);
x_433 = lean_ctor_get(x_414, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_414, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_414, 3);
lean_inc(x_435);
x_436 = lean_ctor_get(x_414, 4);
lean_inc(x_436);
x_437 = lean_ctor_get(x_414, 5);
lean_inc(x_437);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 lean_ctor_release(x_414, 4);
 lean_ctor_release(x_414, 5);
 x_438 = x_414;
} else {
 lean_dec_ref(x_414);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_431, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_431, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_431, 3);
lean_inc(x_441);
x_442 = lean_ctor_get(x_431, 4);
lean_inc(x_442);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 lean_ctor_release(x_431, 4);
 x_443 = x_431;
} else {
 lean_dec_ref(x_431);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(0, 5, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_439);
lean_ctor_set(x_444, 1, x_440);
lean_ctor_set(x_444, 2, x_409);
lean_ctor_set(x_444, 3, x_441);
lean_ctor_set(x_444, 4, x_442);
if (lean_is_scalar(x_438)) {
 x_445 = lean_alloc_ctor(0, 6, 0);
} else {
 x_445 = x_438;
}
lean_ctor_set(x_445, 0, x_433);
lean_ctor_set(x_445, 1, x_434);
lean_ctor_set(x_445, 2, x_444);
lean_ctor_set(x_445, 3, x_435);
lean_ctor_set(x_445, 4, x_436);
lean_ctor_set(x_445, 5, x_437);
if (lean_is_scalar(x_253)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_253;
}
lean_ctor_set(x_446, 0, x_432);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_467 = !lean_is_exclusive(x_246);
if (x_467 == 0)
{
return x_246;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_246, 0);
x_469 = lean_ctor_get(x_246, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_246);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_471 = !lean_is_exclusive(x_24);
if (x_471 == 0)
{
return x_24;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_24, 0);
x_473 = lean_ctor_get(x_24, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_24);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_475 = !lean_is_exclusive(x_20);
if (x_475 == 0)
{
return x_20;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_20, 0);
x_477 = lean_ctor_get(x_20, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_20);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_1, x_8, x_8, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
x_11 = l_Lean_Meta_getFVarLocalDecl(x_10, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_14);
x_15 = l_Lean_Meta_isClassQuick___main(x_14, x_4, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_5 = x_17;
goto _start;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_22 = x_15;
} else {
 lean_dec_ref(x_15);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_85; uint8_t x_86; 
x_29 = lean_ctor_get(x_27, 2);
x_85 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_27, 2, x_85);
x_86 = !lean_is_exclusive(x_4);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_4, 2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_23);
lean_ctor_set(x_88, 1, x_10);
x_89 = lean_array_push(x_87, x_88);
lean_ctor_set(x_4, 2, x_89);
x_90 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_25, x_4, x_21);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_91);
x_30 = x_93;
x_31 = x_92;
goto block_84;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_30 = x_96;
x_31 = x_95;
goto block_84;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_4, 0);
x_98 = lean_ctor_get(x_4, 1);
x_99 = lean_ctor_get(x_4, 2);
x_100 = lean_ctor_get(x_4, 3);
x_101 = lean_ctor_get(x_4, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_4);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_23);
lean_ctor_set(x_102, 1, x_10);
x_103 = lean_array_push(x_99, x_102);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
x_105 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_25, x_104, x_21);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_106);
x_30 = x_108;
x_31 = x_107;
goto block_84;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_109);
x_30 = x_111;
x_31 = x_110;
goto block_84;
}
}
block_84:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 2);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 2);
lean_dec(x_37);
lean_ctor_set(x_32, 2, x_29);
if (lean_is_scalar(x_22)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_22;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
x_41 = lean_ctor_get(x_32, 3);
x_42 = lean_ctor_get(x_32, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_31, 2, x_43);
if (lean_is_scalar(x_22)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_22;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
x_47 = lean_ctor_get(x_31, 3);
x_48 = lean_ctor_get(x_31, 4);
x_49 = lean_ctor_get(x_31, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_32, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_32, 4);
lean_inc(x_53);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_54 = x_32;
} else {
 lean_dec_ref(x_32);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_29);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_49);
if (lean_is_scalar(x_22)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_22;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_31, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_30, 0);
lean_inc(x_59);
lean_dec(x_30);
x_60 = !lean_is_exclusive(x_31);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_31, 2);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_58, 2);
lean_dec(x_63);
lean_ctor_set(x_58, 2, x_29);
if (lean_is_scalar(x_22)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_22;
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_31);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
x_67 = lean_ctor_get(x_58, 3);
x_68 = lean_ctor_get(x_58, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_29);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_31, 2, x_69);
if (lean_is_scalar(x_22)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_22;
}
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_31);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_31, 0);
x_72 = lean_ctor_get(x_31, 1);
x_73 = lean_ctor_get(x_31, 3);
x_74 = lean_ctor_get(x_31, 4);
x_75 = lean_ctor_get(x_31, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_31);
x_76 = lean_ctor_get(x_58, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_58, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_58, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 x_80 = x_58;
} else {
 lean_dec_ref(x_58);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_29);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_72);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_73);
lean_ctor_set(x_82, 4, x_74);
lean_ctor_set(x_82, 5, x_75);
if (lean_is_scalar(x_22)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_22;
}
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_112 = lean_ctor_get(x_27, 0);
x_113 = lean_ctor_get(x_27, 1);
x_114 = lean_ctor_get(x_27, 2);
x_115 = lean_ctor_get(x_27, 3);
x_116 = lean_ctor_get(x_27, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_27);
x_152 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_112);
lean_ctor_set(x_153, 1, x_113);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set(x_153, 4, x_116);
lean_ctor_set(x_21, 2, x_153);
x_154 = lean_ctor_get(x_4, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_4, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_4, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_4, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 4);
lean_inc(x_158);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_159 = x_4;
} else {
 lean_dec_ref(x_4);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_23);
lean_ctor_set(x_160, 1, x_10);
x_161 = lean_array_push(x_156, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_154);
lean_ctor_set(x_162, 1, x_155);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_157);
lean_ctor_set(x_162, 4, x_158);
x_163 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_25, x_162, x_21);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_164);
x_117 = x_166;
x_118 = x_165;
goto block_151;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_167);
x_117 = x_169;
x_118 = x_168;
goto block_151;
}
block_151:
{
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 5);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 4);
lean_inc(x_130);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 x_131 = x_119;
} else {
 lean_dec_ref(x_119);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 5, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_114);
lean_ctor_set(x_132, 3, x_129);
lean_ctor_set(x_132, 4, x_130);
if (lean_is_scalar(x_126)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_126;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_122);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_123);
lean_ctor_set(x_133, 4, x_124);
lean_ctor_set(x_133, 5, x_125);
if (lean_is_scalar(x_22)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_22;
 lean_ctor_set_tag(x_134, 1);
}
lean_ctor_set(x_134, 0, x_120);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_135 = lean_ctor_get(x_118, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_118, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_118, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_118, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_118, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 x_142 = x_118;
} else {
 lean_dec_ref(x_118);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 4);
lean_inc(x_146);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 x_147 = x_135;
} else {
 lean_dec_ref(x_135);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_144);
lean_ctor_set(x_148, 2, x_114);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set(x_148, 4, x_146);
if (lean_is_scalar(x_142)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_142;
}
lean_ctor_set(x_149, 0, x_137);
lean_ctor_set(x_149, 1, x_138);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set(x_149, 4, x_140);
lean_ctor_set(x_149, 5, x_141);
if (lean_is_scalar(x_22)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_22;
}
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_170 = lean_ctor_get(x_21, 2);
x_171 = lean_ctor_get(x_21, 0);
x_172 = lean_ctor_get(x_21, 1);
x_173 = lean_ctor_get(x_21, 3);
x_174 = lean_ctor_get(x_21, 4);
x_175 = lean_ctor_get(x_21, 5);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_170);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_21);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_170, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_170, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 4);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
x_217 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_181)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_181;
}
lean_ctor_set(x_218, 0, x_176);
lean_ctor_set(x_218, 1, x_177);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_179);
lean_ctor_set(x_218, 4, x_180);
x_219 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_219, 0, x_171);
lean_ctor_set(x_219, 1, x_172);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_173);
lean_ctor_set(x_219, 4, x_174);
lean_ctor_set(x_219, 5, x_175);
x_220 = lean_ctor_get(x_4, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_4, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_4, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_4, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_4, 4);
lean_inc(x_224);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_225 = x_4;
} else {
 lean_dec_ref(x_4);
 x_225 = lean_box(0);
}
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_23);
lean_ctor_set(x_226, 1, x_10);
x_227 = lean_array_push(x_222, x_226);
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 5, 0);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_220);
lean_ctor_set(x_228, 1, x_221);
lean_ctor_set(x_228, 2, x_227);
lean_ctor_set(x_228, 3, x_223);
lean_ctor_set(x_228, 4, x_224);
x_229 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_25, x_228, x_219);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_230);
x_182 = x_232;
x_183 = x_231;
goto block_216;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_233);
x_182 = x_235;
x_183 = x_234;
goto block_216;
}
block_216:
{
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_184 = lean_ctor_get(x_183, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 5);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_184, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_184, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_184, 4);
lean_inc(x_195);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 x_196 = x_184;
} else {
 lean_dec_ref(x_184);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 5, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set(x_197, 2, x_178);
lean_ctor_set(x_197, 3, x_194);
lean_ctor_set(x_197, 4, x_195);
if (lean_is_scalar(x_191)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_191;
}
lean_ctor_set(x_198, 0, x_186);
lean_ctor_set(x_198, 1, x_187);
lean_ctor_set(x_198, 2, x_197);
lean_ctor_set(x_198, 3, x_188);
lean_ctor_set(x_198, 4, x_189);
lean_ctor_set(x_198, 5, x_190);
if (lean_is_scalar(x_22)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_22;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_200 = lean_ctor_get(x_183, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_182, 0);
lean_inc(x_201);
lean_dec(x_182);
x_202 = lean_ctor_get(x_183, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_183, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_183, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_183, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_183, 5);
lean_inc(x_206);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 x_207 = x_183;
} else {
 lean_dec_ref(x_183);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_200, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 4);
lean_inc(x_211);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 x_212 = x_200;
} else {
 lean_dec_ref(x_200);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_208);
lean_ctor_set(x_213, 1, x_209);
lean_ctor_set(x_213, 2, x_178);
lean_ctor_set(x_213, 3, x_210);
lean_ctor_set(x_213, 4, x_211);
if (lean_is_scalar(x_207)) {
 x_214 = lean_alloc_ctor(0, 6, 0);
} else {
 x_214 = x_207;
}
lean_ctor_set(x_214, 0, x_202);
lean_ctor_set(x_214, 1, x_203);
lean_ctor_set(x_214, 2, x_213);
lean_ctor_set(x_214, 3, x_204);
lean_ctor_set(x_214, 4, x_205);
lean_ctor_set(x_214, 5, x_206);
if (lean_is_scalar(x_22)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_22;
}
lean_ctor_set(x_215, 0, x_201);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
default: 
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_15, 1);
lean_inc(x_236);
lean_dec(x_15);
lean_inc(x_4);
x_237 = l_Lean_Meta_isClassExpensive___main(x_14, x_4, x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_10);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_nat_add(x_3, x_240);
lean_dec(x_3);
x_3 = x_241;
x_5 = x_239;
goto _start;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_244 = x_237;
} else {
 lean_dec_ref(x_237);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_238, 0);
lean_inc(x_245);
lean_dec(x_238);
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_3, x_246);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_243);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_243, 2);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_307; uint8_t x_308; 
x_251 = lean_ctor_get(x_249, 2);
x_307 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_249, 2, x_307);
x_308 = !lean_is_exclusive(x_4);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_4, 2);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_245);
lean_ctor_set(x_310, 1, x_10);
x_311 = lean_array_push(x_309, x_310);
lean_ctor_set(x_4, 2, x_311);
x_312 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_247, x_4, x_243);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_313);
x_252 = x_315;
x_253 = x_314;
goto block_306;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_312, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
lean_dec(x_312);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_252 = x_318;
x_253 = x_317;
goto block_306;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_4, 0);
x_320 = lean_ctor_get(x_4, 1);
x_321 = lean_ctor_get(x_4, 2);
x_322 = lean_ctor_get(x_4, 3);
x_323 = lean_ctor_get(x_4, 4);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_4);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_245);
lean_ctor_set(x_324, 1, x_10);
x_325 = lean_array_push(x_321, x_324);
x_326 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_326, 0, x_319);
lean_ctor_set(x_326, 1, x_320);
lean_ctor_set(x_326, 2, x_325);
lean_ctor_set(x_326, 3, x_322);
lean_ctor_set(x_326, 4, x_323);
x_327 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_247, x_326, x_243);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_252 = x_330;
x_253 = x_329;
goto block_306;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_327, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_327, 1);
lean_inc(x_332);
lean_dec(x_327);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_331);
x_252 = x_333;
x_253 = x_332;
goto block_306;
}
}
block_306:
{
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_ctor_get(x_253, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_dec(x_252);
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_253, 2);
lean_dec(x_257);
x_258 = !lean_is_exclusive(x_254);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_254, 2);
lean_dec(x_259);
lean_ctor_set(x_254, 2, x_251);
if (lean_is_scalar(x_244)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_244;
 lean_ctor_set_tag(x_260, 1);
}
lean_ctor_set(x_260, 0, x_255);
lean_ctor_set(x_260, 1, x_253);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_254, 0);
x_262 = lean_ctor_get(x_254, 1);
x_263 = lean_ctor_get(x_254, 3);
x_264 = lean_ctor_get(x_254, 4);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_254);
x_265 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_262);
lean_ctor_set(x_265, 2, x_251);
lean_ctor_set(x_265, 3, x_263);
lean_ctor_set(x_265, 4, x_264);
lean_ctor_set(x_253, 2, x_265);
if (lean_is_scalar(x_244)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_244;
 lean_ctor_set_tag(x_266, 1);
}
lean_ctor_set(x_266, 0, x_255);
lean_ctor_set(x_266, 1, x_253);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_267 = lean_ctor_get(x_253, 0);
x_268 = lean_ctor_get(x_253, 1);
x_269 = lean_ctor_get(x_253, 3);
x_270 = lean_ctor_get(x_253, 4);
x_271 = lean_ctor_get(x_253, 5);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_253);
x_272 = lean_ctor_get(x_254, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_254, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_254, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_254, 4);
lean_inc(x_275);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 lean_ctor_release(x_254, 3);
 lean_ctor_release(x_254, 4);
 x_276 = x_254;
} else {
 lean_dec_ref(x_254);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 5, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_272);
lean_ctor_set(x_277, 1, x_273);
lean_ctor_set(x_277, 2, x_251);
lean_ctor_set(x_277, 3, x_274);
lean_ctor_set(x_277, 4, x_275);
x_278 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_278, 0, x_267);
lean_ctor_set(x_278, 1, x_268);
lean_ctor_set(x_278, 2, x_277);
lean_ctor_set(x_278, 3, x_269);
lean_ctor_set(x_278, 4, x_270);
lean_ctor_set(x_278, 5, x_271);
if (lean_is_scalar(x_244)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_244;
 lean_ctor_set_tag(x_279, 1);
}
lean_ctor_set(x_279, 0, x_255);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_280 = lean_ctor_get(x_253, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_252, 0);
lean_inc(x_281);
lean_dec(x_252);
x_282 = !lean_is_exclusive(x_253);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_253, 2);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_280);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_280, 2);
lean_dec(x_285);
lean_ctor_set(x_280, 2, x_251);
if (lean_is_scalar(x_244)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_244;
}
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_253);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_280, 0);
x_288 = lean_ctor_get(x_280, 1);
x_289 = lean_ctor_get(x_280, 3);
x_290 = lean_ctor_get(x_280, 4);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_280);
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_288);
lean_ctor_set(x_291, 2, x_251);
lean_ctor_set(x_291, 3, x_289);
lean_ctor_set(x_291, 4, x_290);
lean_ctor_set(x_253, 2, x_291);
if (lean_is_scalar(x_244)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_244;
}
lean_ctor_set(x_292, 0, x_281);
lean_ctor_set(x_292, 1, x_253);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_293 = lean_ctor_get(x_253, 0);
x_294 = lean_ctor_get(x_253, 1);
x_295 = lean_ctor_get(x_253, 3);
x_296 = lean_ctor_get(x_253, 4);
x_297 = lean_ctor_get(x_253, 5);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_253);
x_298 = lean_ctor_get(x_280, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_280, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_280, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_280, 4);
lean_inc(x_301);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 x_302 = x_280;
} else {
 lean_dec_ref(x_280);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_298);
lean_ctor_set(x_303, 1, x_299);
lean_ctor_set(x_303, 2, x_251);
lean_ctor_set(x_303, 3, x_300);
lean_ctor_set(x_303, 4, x_301);
x_304 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_304, 0, x_293);
lean_ctor_set(x_304, 1, x_294);
lean_ctor_set(x_304, 2, x_303);
lean_ctor_set(x_304, 3, x_295);
lean_ctor_set(x_304, 4, x_296);
lean_ctor_set(x_304, 5, x_297);
if (lean_is_scalar(x_244)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_244;
}
lean_ctor_set(x_305, 0, x_281);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_334 = lean_ctor_get(x_249, 0);
x_335 = lean_ctor_get(x_249, 1);
x_336 = lean_ctor_get(x_249, 2);
x_337 = lean_ctor_get(x_249, 3);
x_338 = lean_ctor_get(x_249, 4);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_249);
x_374 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_375 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_375, 0, x_334);
lean_ctor_set(x_375, 1, x_335);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_337);
lean_ctor_set(x_375, 4, x_338);
lean_ctor_set(x_243, 2, x_375);
x_376 = lean_ctor_get(x_4, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_4, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_4, 2);
lean_inc(x_378);
x_379 = lean_ctor_get(x_4, 3);
lean_inc(x_379);
x_380 = lean_ctor_get(x_4, 4);
lean_inc(x_380);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_381 = x_4;
} else {
 lean_dec_ref(x_4);
 x_381 = lean_box(0);
}
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_245);
lean_ctor_set(x_382, 1, x_10);
x_383 = lean_array_push(x_378, x_382);
if (lean_is_scalar(x_381)) {
 x_384 = lean_alloc_ctor(0, 5, 0);
} else {
 x_384 = x_381;
}
lean_ctor_set(x_384, 0, x_376);
lean_ctor_set(x_384, 1, x_377);
lean_ctor_set(x_384, 2, x_383);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set(x_384, 4, x_380);
x_385 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_247, x_384, x_243);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_388, 0, x_386);
x_339 = x_388;
x_340 = x_387;
goto block_373;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
lean_dec(x_385);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_339 = x_391;
x_340 = x_390;
goto block_373;
}
block_373:
{
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_341 = lean_ctor_get(x_340, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 0);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 3);
lean_inc(x_345);
x_346 = lean_ctor_get(x_340, 4);
lean_inc(x_346);
x_347 = lean_ctor_get(x_340, 5);
lean_inc(x_347);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 lean_ctor_release(x_340, 5);
 x_348 = x_340;
} else {
 lean_dec_ref(x_340);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_341, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_341, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_341, 3);
lean_inc(x_351);
x_352 = lean_ctor_get(x_341, 4);
lean_inc(x_352);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 lean_ctor_release(x_341, 4);
 x_353 = x_341;
} else {
 lean_dec_ref(x_341);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 5, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_349);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_336);
lean_ctor_set(x_354, 3, x_351);
lean_ctor_set(x_354, 4, x_352);
if (lean_is_scalar(x_348)) {
 x_355 = lean_alloc_ctor(0, 6, 0);
} else {
 x_355 = x_348;
}
lean_ctor_set(x_355, 0, x_343);
lean_ctor_set(x_355, 1, x_344);
lean_ctor_set(x_355, 2, x_354);
lean_ctor_set(x_355, 3, x_345);
lean_ctor_set(x_355, 4, x_346);
lean_ctor_set(x_355, 5, x_347);
if (lean_is_scalar(x_244)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_244;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_342);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_357 = lean_ctor_get(x_340, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_339, 0);
lean_inc(x_358);
lean_dec(x_339);
x_359 = lean_ctor_get(x_340, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_340, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_340, 3);
lean_inc(x_361);
x_362 = lean_ctor_get(x_340, 4);
lean_inc(x_362);
x_363 = lean_ctor_get(x_340, 5);
lean_inc(x_363);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 lean_ctor_release(x_340, 4);
 lean_ctor_release(x_340, 5);
 x_364 = x_340;
} else {
 lean_dec_ref(x_340);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_357, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_357, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_357, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_357, 4);
lean_inc(x_368);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 x_369 = x_357;
} else {
 lean_dec_ref(x_357);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 5, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_365);
lean_ctor_set(x_370, 1, x_366);
lean_ctor_set(x_370, 2, x_336);
lean_ctor_set(x_370, 3, x_367);
lean_ctor_set(x_370, 4, x_368);
if (lean_is_scalar(x_364)) {
 x_371 = lean_alloc_ctor(0, 6, 0);
} else {
 x_371 = x_364;
}
lean_ctor_set(x_371, 0, x_359);
lean_ctor_set(x_371, 1, x_360);
lean_ctor_set(x_371, 2, x_370);
lean_ctor_set(x_371, 3, x_361);
lean_ctor_set(x_371, 4, x_362);
lean_ctor_set(x_371, 5, x_363);
if (lean_is_scalar(x_244)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_244;
}
lean_ctor_set(x_372, 0, x_358);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_392 = lean_ctor_get(x_243, 2);
x_393 = lean_ctor_get(x_243, 0);
x_394 = lean_ctor_get(x_243, 1);
x_395 = lean_ctor_get(x_243, 3);
x_396 = lean_ctor_get(x_243, 4);
x_397 = lean_ctor_get(x_243, 5);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_392);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_243);
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 3);
lean_inc(x_401);
x_402 = lean_ctor_get(x_392, 4);
lean_inc(x_402);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 x_403 = x_392;
} else {
 lean_dec_ref(x_392);
 x_403 = lean_box(0);
}
x_439 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_403)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_403;
}
lean_ctor_set(x_440, 0, x_398);
lean_ctor_set(x_440, 1, x_399);
lean_ctor_set(x_440, 2, x_439);
lean_ctor_set(x_440, 3, x_401);
lean_ctor_set(x_440, 4, x_402);
x_441 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_441, 0, x_393);
lean_ctor_set(x_441, 1, x_394);
lean_ctor_set(x_441, 2, x_440);
lean_ctor_set(x_441, 3, x_395);
lean_ctor_set(x_441, 4, x_396);
lean_ctor_set(x_441, 5, x_397);
x_442 = lean_ctor_get(x_4, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_4, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_4, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_4, 3);
lean_inc(x_445);
x_446 = lean_ctor_get(x_4, 4);
lean_inc(x_446);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_447 = x_4;
} else {
 lean_dec_ref(x_4);
 x_447 = lean_box(0);
}
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_245);
lean_ctor_set(x_448, 1, x_10);
x_449 = lean_array_push(x_444, x_448);
if (lean_is_scalar(x_447)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_447;
}
lean_ctor_set(x_450, 0, x_442);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_449);
lean_ctor_set(x_450, 3, x_445);
lean_ctor_set(x_450, 4, x_446);
x_451 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_247, x_450, x_441);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_452);
x_404 = x_454;
x_405 = x_453;
goto block_438;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_451, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
lean_dec(x_451);
x_457 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_457, 0, x_455);
x_404 = x_457;
x_405 = x_456;
goto block_438;
}
block_438:
{
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_406 = lean_ctor_get(x_405, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
lean_dec(x_404);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_405, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_405, 4);
lean_inc(x_411);
x_412 = lean_ctor_get(x_405, 5);
lean_inc(x_412);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 lean_ctor_release(x_405, 4);
 lean_ctor_release(x_405, 5);
 x_413 = x_405;
} else {
 lean_dec_ref(x_405);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_406, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_406, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_406, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_406, 4);
lean_inc(x_417);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 lean_ctor_release(x_406, 4);
 x_418 = x_406;
} else {
 lean_dec_ref(x_406);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 5, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_414);
lean_ctor_set(x_419, 1, x_415);
lean_ctor_set(x_419, 2, x_400);
lean_ctor_set(x_419, 3, x_416);
lean_ctor_set(x_419, 4, x_417);
if (lean_is_scalar(x_413)) {
 x_420 = lean_alloc_ctor(0, 6, 0);
} else {
 x_420 = x_413;
}
lean_ctor_set(x_420, 0, x_408);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_419);
lean_ctor_set(x_420, 3, x_410);
lean_ctor_set(x_420, 4, x_411);
lean_ctor_set(x_420, 5, x_412);
if (lean_is_scalar(x_244)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_244;
 lean_ctor_set_tag(x_421, 1);
}
lean_ctor_set(x_421, 0, x_407);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_422 = lean_ctor_get(x_405, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_404, 0);
lean_inc(x_423);
lean_dec(x_404);
x_424 = lean_ctor_get(x_405, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_405, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_405, 3);
lean_inc(x_426);
x_427 = lean_ctor_get(x_405, 4);
lean_inc(x_427);
x_428 = lean_ctor_get(x_405, 5);
lean_inc(x_428);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 lean_ctor_release(x_405, 4);
 lean_ctor_release(x_405, 5);
 x_429 = x_405;
} else {
 lean_dec_ref(x_405);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_422, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_422, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_422, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_422, 4);
lean_inc(x_433);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 lean_ctor_release(x_422, 3);
 lean_ctor_release(x_422, 4);
 x_434 = x_422;
} else {
 lean_dec_ref(x_422);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 5, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_400);
lean_ctor_set(x_435, 3, x_432);
lean_ctor_set(x_435, 4, x_433);
if (lean_is_scalar(x_429)) {
 x_436 = lean_alloc_ctor(0, 6, 0);
} else {
 x_436 = x_429;
}
lean_ctor_set(x_436, 0, x_424);
lean_ctor_set(x_436, 1, x_425);
lean_ctor_set(x_436, 2, x_435);
lean_ctor_set(x_436, 3, x_426);
lean_ctor_set(x_436, 4, x_427);
lean_ctor_set(x_436, 5, x_428);
if (lean_is_scalar(x_244)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_244;
}
lean_ctor_set(x_437, 0, x_423);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_458 = !lean_is_exclusive(x_237);
if (x_458 == 0)
{
return x_237;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_237, 0);
x_460 = lean_ctor_get(x_237, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_237);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_462 = !lean_is_exclusive(x_15);
if (x_462 == 0)
{
return x_15;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_15, 0);
x_464 = lean_ctor_get(x_15, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_15);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_466 = !lean_is_exclusive(x_11);
if (x_466 == 0)
{
return x_11;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_11, 0);
x_468 = lean_ctor_get(x_11, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_11);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_6) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_27 = lean_array_get_size(x_4);
x_28 = lean_expr_instantiate_rev_range(x_24, x_5, x_27, x_4);
lean_dec(x_27);
lean_dec(x_24);
x_29 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = (uint8_t)((x_26 << 24) >> 61);
lean_inc(x_30);
x_33 = lean_local_ctx_mk_local_decl(x_3, x_30, x_23, x_28, x_32);
x_34 = l_Lean_mkFVar(x_30);
x_35 = lean_array_push(x_4, x_34);
x_3 = x_33;
x_4 = x_35;
x_6 = x_25;
x_8 = x_31;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 2);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_array_get_size(x_4);
x_43 = lean_nat_dec_lt(x_42, x_41);
lean_dec(x_41);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_7, 1);
lean_dec(x_45);
lean_ctor_set(x_7, 1, x_3);
x_46 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_4, x_4, x_5, x_7, x_8);
lean_dec(x_4);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 2);
x_49 = lean_ctor_get(x_7, 3);
x_50 = lean_ctor_get(x_7, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_3);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_50);
x_52 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_4, x_4, x_5, x_51, x_8);
lean_dec(x_4);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_expr_instantiate_rev_range(x_38, x_5, x_42, x_4);
lean_dec(x_42);
lean_dec(x_38);
x_54 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = (uint8_t)((x_40 << 24) >> 61);
lean_inc(x_55);
x_58 = lean_local_ctx_mk_local_decl(x_3, x_55, x_37, x_53, x_57);
x_59 = l_Lean_mkFVar(x_55);
x_60 = lean_array_push(x_4, x_59);
x_3 = x_58;
x_4 = x_60;
x_6 = x_39;
x_8 = x_56;
goto _start;
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_9 = x_62;
goto block_22;
}
block_22:
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = lean_array_get_size(x_4);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_3);
if (x_1 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_4, x_4, x_5, x_7, x_8);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_4, x_5, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
lean_inc(x_3);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
if (x_1 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_4, x_4, x_5, x_19, x_8);
lean_dec(x_4);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_4, x_5, x_19, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_whnf(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Expr_isForall(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = l_Array_empty___closed__1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_9, x_9, x_10, x_10, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Array_empty___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(x_13, x_2, x_12, x_14, x_15, x_6, x_3, x_7);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_8, 4, x_12);
x_13 = l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(x_5, x_7, x_11, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_15, x_10);
lean_ctor_set(x_13, 1, x_16);
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
x_19 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_18, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_10);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
lean_inc(x_2);
x_28 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_26);
x_29 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_27, x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
x_33 = lean_ctor_get(x_8, 2);
x_34 = lean_ctor_get(x_8, 3);
x_35 = lean_ctor_get(x_8, 4);
x_36 = lean_ctor_get(x_8, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = l_Lean_TraceState_Inhabited___closed__1;
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_36);
x_40 = l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(x_5, x_7, x_37, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_42, x_35);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_48 = x_40;
} else {
 lean_dec_ref(x_40);
 x_48 = lean_box(0);
}
lean_inc(x_2);
x_49 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_46);
x_50 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_47, x_35);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_List_map___main___at_Lean_MessageData_coeOfListExpr___spec__1(x_1);
x_6 = l_Lean_MessageData_ofList(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_Term_throwError___rarg(x_8, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Match_15__processVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern variable, must be atomic");
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
x_1 = lean_mk_string("invalid pattern, variable '");
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
x_1 = lean_mk_string("' occurred more than once");
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
lean_object* l___private_Lean_Elab_Match_15__processVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (x_2 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_3);
x_6 = x_69;
x_7 = x_5;
goto block_67;
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_1);
x_70 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_3, x_4, x_5);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
block_67:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = l_Lean_Name_eraseMacroScopes(x_1);
x_12 = l_Lean_Name_isAtomic(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_6);
lean_dec(x_9);
lean_dec(x_1);
x_13 = l___private_Lean_Elab_Match_15__processVar___closed__3;
x_14 = l_Lean_Elab_Term_throwError___rarg(x_13, x_4, x_7);
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
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
x_20 = l_Lean_NameSet_contains(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_21 = lean_box(0);
lean_inc(x_1);
x_22 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_19, x_1, x_21);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_19);
lean_free_object(x_6);
lean_dec(x_9);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_1);
x_29 = l___private_Lean_Elab_Match_15__processVar___closed__6;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_Match_15__processVar___closed__9;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Term_throwError___rarg(x_32, x_4, x_7);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = l_Lean_Name_eraseMacroScopes(x_1);
x_40 = l_Lean_Name_isAtomic(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_38);
lean_dec(x_1);
x_41 = l___private_Lean_Elab_Match_15__processVar___closed__3;
x_42 = l_Lean_Elab_Term_throwError___rarg(x_41, x_4, x_7);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
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
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = l_Lean_NameSet_contains(x_47, x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_49 = lean_box(0);
lean_inc(x_1);
x_50 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_47, x_1, x_49);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_dec(x_38);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_1);
x_53 = lean_array_push(x_51, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_47);
lean_dec(x_38);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_1);
x_58 = l___private_Lean_Elab_Match_15__processVar___closed__6;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l___private_Lean_Elab_Match_15__processVar___closed__9;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Elab_Term_throwError___rarg(x_61, x_4, x_7);
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
}
}
}
}
lean_object* l___private_Lean_Elab_Match_15__processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Match_15__processVar(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_40; 
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
lean_dec(x_4);
lean_inc(x_31);
lean_inc(x_3);
x_40 = lean_environment_find(x_3, x_31);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_3);
x_41 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_5, x_6, x_7);
lean_dec(x_5);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 6)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_31);
lean_dec(x_3);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(x_43, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_42);
x_56 = lean_box(0);
x_32 = x_56;
goto block_39;
}
}
block_39:
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_32);
x_33 = l_Lean_EqnCompiler_matchPatternAttr;
x_34 = l_Lean_TagAttribute_hasTag(x_33, x_3, x_31);
lean_dec(x_31);
lean_dec(x_3);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_8 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_box(0);
x_8 = x_57;
goto block_30;
}
block_30:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
x_9 = l_Lean_Syntax_getId(x_1);
x_10 = l___private_Lean_Elab_Match_15__processVar(x_9, x_2, x_5, x_6, x_7);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_12, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
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
}
lean_object* l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(lean_object* x_1) {
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
x_6 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(x_5);
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
x_10 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(x_9);
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
lean_object* l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_4(x_2, x_9, x_10, x_4, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4___rarg), 5, 0);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_1, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1;
x_2 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_box(0);
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_resolveName(x_8, x_9, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_12, x_10);
x_15 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_Match_15__processVar(x_16, x_3, x_5, x_6, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_19, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
lean_dec(x_15);
x_39 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_3, x_4, x_38, x_5, x_6, x_13);
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_1);
x_40 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_15, x_5, x_6, x_13);
lean_dec(x_5);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_dec(x_11);
x_42 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2;
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_43 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_44 = l___private_Lean_Elab_Match_15__processVar(x_43, x_3, x_5, x_6, x_41);
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
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_46, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = l_Lean_Elab_Term_CollectPatternVars_processIdAuxAux(x_1, x_3, x_4, x_65, x_5, x_6, x_41);
lean_dec(x_1);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_4);
lean_dec(x_1);
x_67 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_42, x_5, x_6, x_41);
lean_dec(x_5);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_4);
lean_dec(x_1);
x_68 = l_Nat_Inhabited;
x_69 = l_monadInhabited___rarg(x_2, x_68);
x_70 = l_unreachable_x21___rarg(x_69);
x_71 = lean_apply_3(x_70, x_5, x_6, x_7);
return x_71;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8;
x_2 = lean_alloc_closure((void*)(l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1___rarg), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_7 = lean_box(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_16__processIdAux___lambda__1___boxed), 7, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
x_9 = l___private_Lean_Elab_Match_16__processIdAux___closed__1;
x_10 = lean_alloc_closure((void*)(l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4___rarg), 5, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Term_CollectPatternVars_withRef___rarg(x_1, x_10, x_3, x_4, x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Match_16__processIdAux(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_17__processCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l___private_Lean_Elab_Match_16__processIdAux(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_18__processId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l___private_Lean_Elab_Match_16__processIdAux(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
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
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3;
x_5 = l_Lean_Elab_Term_throwError___rarg(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_fget(x_1, x_3);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_mod(x_3, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_19 = lean_array_push(x_4, x_12);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_inc(x_2);
lean_inc(x_6);
x_21 = lean_apply_4(x_2, x_12, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_28 = lean_array_push(x_4, x_24);
x_3 = x_27;
x_4 = x_28;
x_5 = x_25;
x_7 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(x_1, x_2, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("named parameters are not allowed in patterns");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3;
x_20 = l_Lean_Elab_Term_throwErrorAt___rarg(x_12, x_19, x_5, x_6);
lean_dec(x_12);
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
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_fget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_3, x_2, x_13);
x_15 = x_12;
x_16 = lean_nat_dec_lt(x_2, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_5);
x_17 = l___private_Lean_Elab_Match_20__collect___main(x_15, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_14, x_2, x_24);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_25;
x_4 = x_21;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_2, x_31);
x_33 = x_15;
x_34 = lean_array_fset(x_14, x_2, x_33);
lean_dec(x_2);
x_2 = x_32;
x_3 = x_34;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l___private_Lean_Elab_Match_20__collect___main(x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Syntax_setArg(x_1, x_5, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_Syntax_setArg(x_1, x_5, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = l_Lean_Syntax_setArg(x_1, x_5, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, notation is ambiguous");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_20__collect___main), 4, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid struct instance pattern, 'with' is not allowed in patterns");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_20__collect___main___lambda__1), 4, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_ctor_set(x_9, 5, x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 8);
lean_dec(x_15);
lean_ctor_set(x_8, 8, x_11);
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_inc(x_2);
x_17 = lean_name_mk_string(x_2, x_16);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_inc(x_2);
x_20 = lean_name_mk_string(x_2, x_19);
x_21 = lean_name_eq(x_3, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_mkHole___closed__1;
lean_inc(x_2);
x_23 = lean_name_mk_string(x_2, x_22);
x_24 = lean_name_eq(x_3, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
lean_inc(x_2);
x_26 = lean_name_mk_string(x_2, x_25);
x_27 = lean_name_eq(x_3, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
x_28 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_inc(x_2);
x_29 = lean_name_mk_string(x_2, x_28);
x_30 = lean_name_eq(x_3, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_inc(x_2);
x_32 = lean_name_mk_string(x_2, x_31);
x_33 = lean_name_eq(x_3, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_5);
x_34 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
x_35 = lean_name_mk_string(x_2, x_34);
x_36 = lean_name_eq(x_3, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_strLitKind;
x_38 = lean_name_eq(x_3, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_numLitKind;
x_40 = lean_name_eq(x_3, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_charLitKind;
x_42 = lean_name_eq(x_3, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_4);
x_43 = l_Lean_choiceKind;
x_44 = lean_name_eq(x_3, x_43);
lean_dec(x_3);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_8, x_9);
lean_dec(x_7);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_7);
x_46 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
x_47 = l_Lean_Elab_Term_throwError___rarg(x_46, x_8, x_9);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_9);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_9);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_8);
lean_dec(x_3);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_7);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_9);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_7);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_9);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Syntax_getArg(x_4, x_60);
x_62 = l_Lean_Syntax_getId(x_61);
x_63 = 0;
lean_inc(x_8);
x_64 = l___private_Lean_Elab_Match_15__processVar(x_62, x_63, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(2u);
x_69 = l_Lean_Syntax_getArg(x_4, x_68);
lean_dec(x_4);
lean_inc(x_8);
x_70 = l___private_Lean_Elab_Match_20__collect___main(x_69, x_67, x_8, x_66);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_72);
lean_dec(x_8);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_getMainModule___rarg(x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_82 = l_Lean_addMacroScope(x_80, x_81, x_76);
x_83 = l_Lean_SourceInfo_inhabited___closed__1;
x_84 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_85 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_82);
lean_ctor_set(x_86, 3, x_85);
x_87 = l_Array_empty___closed__1;
x_88 = lean_array_push(x_87, x_86);
x_89 = lean_array_push(x_87, x_61);
x_90 = lean_array_push(x_89, x_74);
x_91 = l_Lean_nullKind___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_88, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_5);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_71, 0, x_94);
lean_ctor_set(x_78, 0, x_71);
return x_78;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_ctor_get(x_78, 0);
x_96 = lean_ctor_get(x_78, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_78);
x_97 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_98 = l_Lean_addMacroScope(x_95, x_97, x_76);
x_99 = l_Lean_SourceInfo_inhabited___closed__1;
x_100 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_101 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_98);
lean_ctor_set(x_102, 3, x_101);
x_103 = l_Array_empty___closed__1;
x_104 = lean_array_push(x_103, x_102);
x_105 = lean_array_push(x_103, x_61);
x_106 = lean_array_push(x_105, x_74);
x_107 = l_Lean_nullKind___closed__2;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_104, x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_5);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_71, 0, x_110);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_71);
lean_ctor_set(x_111, 1, x_96);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_112 = lean_ctor_get(x_71, 0);
x_113 = lean_ctor_get(x_71, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_71);
x_114 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_72);
lean_dec(x_8);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Elab_Term_getMainModule___rarg(x_116);
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
x_121 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_122 = l_Lean_addMacroScope(x_118, x_121, x_115);
x_123 = l_Lean_SourceInfo_inhabited___closed__1;
x_124 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_125 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_126 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_122);
lean_ctor_set(x_126, 3, x_125);
x_127 = l_Array_empty___closed__1;
x_128 = lean_array_push(x_127, x_126);
x_129 = lean_array_push(x_127, x_61);
x_130 = lean_array_push(x_129, x_112);
x_131 = l_Lean_nullKind___closed__2;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_push(x_128, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_5);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_113);
if (lean_is_scalar(x_120)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_120;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_119);
return x_136;
}
}
else
{
uint8_t x_137; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_5);
x_137 = !lean_is_exclusive(x_70);
if (x_137 == 0)
{
return x_70;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_70, 0);
x_139 = lean_ctor_get(x_70, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_70);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_141 = !lean_is_exclusive(x_64);
if (x_141 == 0)
{
return x_64;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_64, 0);
x_143 = lean_ctor_get(x_64, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_64);
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
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Syntax_getArg(x_4, x_145);
x_147 = 1;
x_148 = l___private_Lean_Elab_Match_16__processIdAux(x_146, x_147, x_7, x_8, x_9);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_150, 0);
lean_dec(x_152);
lean_ctor_set(x_150, 0, x_4);
return x_148;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_4);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_148, 0, x_154);
return x_148;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_148, 0);
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_148);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_4);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
return x_160;
}
}
else
{
uint8_t x_161; 
lean_dec(x_4);
x_161 = !lean_is_exclusive(x_148);
if (x_161 == 0)
{
return x_148;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_148, 0);
x_163 = lean_ctor_get(x_148, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_148);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_dec(x_5);
x_165 = l_Lean_Syntax_inhabited;
x_166 = lean_array_get(x_165, x_6, x_12);
x_167 = l_Lean_Syntax_isNone(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_dec(x_4);
x_168 = lean_unsigned_to_nat(0u);
x_169 = l_Lean_Syntax_getArg(x_166, x_168);
x_170 = l_Lean_Syntax_getArg(x_166, x_12);
x_171 = l_Lean_Syntax_isNone(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_172 = l_Lean_Syntax_getArg(x_170, x_168);
x_173 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_174 = lean_name_mk_string(x_2, x_173);
lean_inc(x_172);
x_175 = l_Lean_Syntax_isOfKind(x_172, x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; 
lean_inc(x_8);
x_176 = l___private_Lean_Elab_Match_20__collect___main(x_169, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = l_Lean_Syntax_setArg(x_166, x_168, x_179);
x_182 = l_Lean_Syntax_getArg(x_172, x_12);
x_183 = l_Lean_Syntax_getArgs(x_182);
lean_dec(x_182);
x_184 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_185 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_183, x_184, x_180, x_8, x_178);
lean_dec(x_183);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = l_Lean_nullKind;
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = l_Lean_Syntax_setArg(x_172, x_12, x_191);
x_193 = l_Lean_Syntax_setArg(x_170, x_168, x_192);
x_194 = l_Lean_Syntax_setArg(x_181, x_12, x_193);
x_195 = lean_array_set(x_6, x_12, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_3);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_187, 0, x_196);
return x_185;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_197 = lean_ctor_get(x_187, 0);
x_198 = lean_ctor_get(x_187, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_187);
x_199 = l_Lean_nullKind;
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
x_201 = l_Lean_Syntax_setArg(x_172, x_12, x_200);
x_202 = l_Lean_Syntax_setArg(x_170, x_168, x_201);
x_203 = l_Lean_Syntax_setArg(x_181, x_12, x_202);
x_204 = lean_array_set(x_6, x_12, x_203);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_3);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_198);
lean_ctor_set(x_185, 0, x_206);
return x_185;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_207 = lean_ctor_get(x_185, 0);
x_208 = lean_ctor_get(x_185, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_185);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
x_212 = l_Lean_nullKind;
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_209);
x_214 = l_Lean_Syntax_setArg(x_172, x_12, x_213);
x_215 = l_Lean_Syntax_setArg(x_170, x_168, x_214);
x_216 = l_Lean_Syntax_setArg(x_181, x_12, x_215);
x_217 = lean_array_set(x_6, x_12, x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_3);
lean_ctor_set(x_218, 1, x_217);
if (lean_is_scalar(x_211)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_211;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_210);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_208);
return x_220;
}
}
else
{
uint8_t x_221; 
lean_dec(x_181);
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_6);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_185);
if (x_221 == 0)
{
return x_185;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_185, 0);
x_223 = lean_ctor_get(x_185, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_185);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_176);
if (x_225 == 0)
{
return x_176;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_176, 0);
x_227 = lean_ctor_get(x_176, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_176);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_object* x_229; 
lean_dec(x_172);
lean_dec(x_170);
x_229 = l___private_Lean_Elab_Match_20__collect___main(x_169, x_7, x_8, x_9);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = l_Lean_Syntax_setArg(x_166, x_168, x_233);
x_235 = lean_array_set(x_6, x_12, x_234);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_3);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_231, 0, x_236);
return x_229;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_ctor_get(x_231, 0);
x_238 = lean_ctor_get(x_231, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_231);
x_239 = l_Lean_Syntax_setArg(x_166, x_168, x_237);
x_240 = lean_array_set(x_6, x_12, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_3);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
lean_ctor_set(x_229, 0, x_242);
return x_229;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_243 = lean_ctor_get(x_229, 0);
x_244 = lean_ctor_get(x_229, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_229);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_247 = x_243;
} else {
 lean_dec_ref(x_243);
 x_247 = lean_box(0);
}
x_248 = l_Lean_Syntax_setArg(x_166, x_168, x_245);
x_249 = lean_array_set(x_6, x_12, x_248);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_3);
lean_ctor_set(x_250, 1, x_249);
if (lean_is_scalar(x_247)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_247;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_246);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_244);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_229);
if (x_253 == 0)
{
return x_229;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_229, 0);
x_255 = lean_ctor_get(x_229, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_229);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
else
{
lean_object* x_257; 
lean_dec(x_170);
lean_dec(x_2);
x_257 = l___private_Lean_Elab_Match_20__collect___main(x_169, x_7, x_8, x_9);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_257, 0);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = l_Lean_Syntax_setArg(x_166, x_168, x_261);
x_263 = lean_array_set(x_6, x_12, x_262);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_3);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_259, 0, x_264);
return x_257;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_259, 0);
x_266 = lean_ctor_get(x_259, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_259);
x_267 = l_Lean_Syntax_setArg(x_166, x_168, x_265);
x_268 = lean_array_set(x_6, x_12, x_267);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_3);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set(x_257, 0, x_270);
return x_257;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_271 = lean_ctor_get(x_257, 0);
x_272 = lean_ctor_get(x_257, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_257);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_275 = x_271;
} else {
 lean_dec_ref(x_271);
 x_275 = lean_box(0);
}
x_276 = l_Lean_Syntax_setArg(x_166, x_168, x_273);
x_277 = lean_array_set(x_6, x_12, x_276);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_3);
lean_ctor_set(x_278, 1, x_277);
if (lean_is_scalar(x_275)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_275;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_274);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_272);
return x_280;
}
}
else
{
uint8_t x_281; 
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_3);
x_281 = !lean_is_exclusive(x_257);
if (x_281 == 0)
{
return x_257;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_257, 0);
x_283 = lean_ctor_get(x_257, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_257);
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
lean_object* x_285; lean_object* x_286; 
lean_dec(x_166);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_4);
lean_ctor_set(x_285, 1, x_7);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_9);
return x_286;
}
}
}
else
{
lean_object* x_287; uint8_t x_288; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_287 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_8, x_9);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_7);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_290 = lean_ctor_get(x_287, 0);
x_291 = lean_ctor_get(x_7, 1);
x_292 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_290);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_array_push(x_291, x_293);
lean_ctor_set(x_7, 1, x_294);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_7);
lean_ctor_set(x_287, 0, x_295);
return x_287;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_296 = lean_ctor_get(x_287, 0);
x_297 = lean_ctor_get(x_7, 0);
x_298 = lean_ctor_get(x_7, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_7);
x_299 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_296);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_array_push(x_298, x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_297);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_296);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set(x_287, 0, x_303);
return x_287;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_287, 0);
x_305 = lean_ctor_get(x_287, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_287);
x_306 = lean_ctor_get(x_7, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_7, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_308 = x_7;
} else {
 lean_dec_ref(x_7);
 x_308 = lean_box(0);
}
x_309 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_304);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_array_push(x_307, x_310);
if (lean_is_scalar(x_308)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_308;
}
lean_ctor_set(x_312, 0, x_306);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_304);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_305);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_315 = l_Lean_Syntax_inhabited;
x_316 = lean_array_get(x_315, x_6, x_12);
x_317 = l_Lean_Syntax_isNone(x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_318 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
x_319 = l_Lean_Elab_Term_throwErrorAt___rarg(x_316, x_318, x_8, x_9);
lean_dec(x_316);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
return x_319;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_319, 0);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_319);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_316);
x_324 = lean_unsigned_to_nat(2u);
x_325 = lean_array_get(x_315, x_6, x_324);
x_326 = l_Lean_Syntax_getArgs(x_325);
lean_dec(x_325);
x_327 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
x_328 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_326, x_327, x_7, x_8, x_9);
lean_dec(x_326);
if (lean_obj_tag(x_328) == 0)
{
uint8_t x_329; 
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = !lean_is_exclusive(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_330, 0);
x_333 = l_Lean_nullKind;
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
x_335 = lean_array_set(x_6, x_324, x_334);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_3);
lean_ctor_set(x_336, 1, x_335);
lean_ctor_set(x_330, 0, x_336);
return x_328;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_330, 0);
x_338 = lean_ctor_get(x_330, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_330);
x_339 = l_Lean_nullKind;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_337);
x_341 = lean_array_set(x_6, x_324, x_340);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_3);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_338);
lean_ctor_set(x_328, 0, x_343);
return x_328;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_344 = lean_ctor_get(x_328, 0);
x_345 = lean_ctor_get(x_328, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_328);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
x_349 = l_Lean_nullKind;
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_346);
x_351 = lean_array_set(x_6, x_324, x_350);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_3);
lean_ctor_set(x_352, 1, x_351);
if (lean_is_scalar(x_348)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_348;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_347);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_345);
return x_354;
}
}
else
{
uint8_t x_355; 
lean_dec(x_6);
lean_dec(x_3);
x_355 = !lean_is_exclusive(x_328);
if (x_355 == 0)
{
return x_328;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_328, 0);
x_357 = lean_ctor_get(x_328, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_328);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_359 = l_Lean_Syntax_inhabited;
x_360 = lean_array_get(x_359, x_6, x_12);
x_361 = l_Lean_Syntax_getArgs(x_360);
lean_dec(x_360);
x_362 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_363 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_361, x_362, x_7, x_8, x_9);
lean_dec(x_361);
if (lean_obj_tag(x_363) == 0)
{
uint8_t x_364; 
x_364 = !lean_is_exclusive(x_363);
if (x_364 == 0)
{
lean_object* x_365; uint8_t x_366; 
x_365 = lean_ctor_get(x_363, 0);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_367 = lean_ctor_get(x_365, 0);
x_368 = l_Lean_nullKind;
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
x_370 = lean_array_set(x_6, x_12, x_369);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_3);
lean_ctor_set(x_371, 1, x_370);
lean_ctor_set(x_365, 0, x_371);
return x_363;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_372 = lean_ctor_get(x_365, 0);
x_373 = lean_ctor_get(x_365, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_365);
x_374 = l_Lean_nullKind;
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_372);
x_376 = lean_array_set(x_6, x_12, x_375);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_3);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_373);
lean_ctor_set(x_363, 0, x_378);
return x_363;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_379 = lean_ctor_get(x_363, 0);
x_380 = lean_ctor_get(x_363, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_363);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_383 = x_379;
} else {
 lean_dec_ref(x_379);
 x_383 = lean_box(0);
}
x_384 = l_Lean_nullKind;
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_381);
x_386 = lean_array_set(x_6, x_12, x_385);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_3);
lean_ctor_set(x_387, 1, x_386);
if (lean_is_scalar(x_383)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_383;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_382);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_380);
return x_389;
}
}
else
{
uint8_t x_390; 
lean_dec(x_6);
lean_dec(x_3);
x_390 = !lean_is_exclusive(x_363);
if (x_390 == 0)
{
return x_363;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_363, 0);
x_392 = lean_ctor_get(x_363, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_363);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_5);
lean_dec(x_4);
x_394 = l_Lean_Syntax_inhabited;
x_395 = lean_unsigned_to_nat(0u);
x_396 = lean_array_get(x_394, x_6, x_395);
x_397 = lean_array_get(x_394, x_6, x_12);
x_398 = l_Lean_Syntax_getArgs(x_397);
lean_dec(x_397);
lean_inc(x_8);
x_399 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_2, x_398, x_395, x_7, x_8, x_9);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = 1;
lean_inc(x_8);
x_404 = l___private_Lean_Elab_Match_16__processIdAux(x_396, x_403, x_402, x_8, x_401);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_409 = x_398;
x_410 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed), 6, 3);
lean_closure_set(x_410, 0, x_407);
lean_closure_set(x_410, 1, x_395);
lean_closure_set(x_410, 2, x_409);
x_411 = x_410;
x_412 = lean_apply_3(x_411, x_408, x_8, x_406);
if (lean_obj_tag(x_412) == 0)
{
uint8_t x_413; 
x_413 = !lean_is_exclusive(x_412);
if (x_413 == 0)
{
lean_object* x_414; uint8_t x_415; 
x_414 = lean_ctor_get(x_412, 0);
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_414, 0);
x_417 = l_Lean_nullKind;
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_array_set(x_6, x_12, x_418);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_3);
lean_ctor_set(x_420, 1, x_419);
lean_ctor_set(x_414, 0, x_420);
return x_412;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_421 = lean_ctor_get(x_414, 0);
x_422 = lean_ctor_get(x_414, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_414);
x_423 = l_Lean_nullKind;
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_421);
x_425 = lean_array_set(x_6, x_12, x_424);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_3);
lean_ctor_set(x_426, 1, x_425);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_422);
lean_ctor_set(x_412, 0, x_427);
return x_412;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_428 = lean_ctor_get(x_412, 0);
x_429 = lean_ctor_get(x_412, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_412);
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_432 = x_428;
} else {
 lean_dec_ref(x_428);
 x_432 = lean_box(0);
}
x_433 = l_Lean_nullKind;
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_430);
x_435 = lean_array_set(x_6, x_12, x_434);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_3);
lean_ctor_set(x_436, 1, x_435);
if (lean_is_scalar(x_432)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_432;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_431);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_429);
return x_438;
}
}
else
{
uint8_t x_439; 
lean_dec(x_6);
lean_dec(x_3);
x_439 = !lean_is_exclusive(x_412);
if (x_439 == 0)
{
return x_412;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_412, 0);
x_441 = lean_ctor_get(x_412, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_412);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
uint8_t x_443; 
lean_dec(x_398);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_443 = !lean_is_exclusive(x_404);
if (x_443 == 0)
{
return x_404;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_404, 0);
x_445 = lean_ctor_get(x_404, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_404);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_398);
lean_dec(x_396);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_447 = !lean_is_exclusive(x_399);
if (x_447 == 0)
{
return x_399;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_399, 0);
x_449 = lean_ctor_get(x_399, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_399);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; 
x_451 = lean_ctor_get(x_8, 0);
x_452 = lean_ctor_get(x_8, 1);
x_453 = lean_ctor_get(x_8, 2);
x_454 = lean_ctor_get(x_8, 3);
x_455 = lean_ctor_get(x_8, 4);
x_456 = lean_ctor_get(x_8, 5);
x_457 = lean_ctor_get(x_8, 6);
x_458 = lean_ctor_get(x_8, 7);
x_459 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_460 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_461 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_462 = lean_ctor_get(x_8, 9);
lean_inc(x_462);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_8);
x_463 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_463, 0, x_451);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set(x_463, 4, x_455);
lean_ctor_set(x_463, 5, x_456);
lean_ctor_set(x_463, 6, x_457);
lean_ctor_set(x_463, 7, x_458);
lean_ctor_set(x_463, 8, x_11);
lean_ctor_set(x_463, 9, x_462);
lean_ctor_set_uint8(x_463, sizeof(void*)*10, x_459);
lean_ctor_set_uint8(x_463, sizeof(void*)*10 + 1, x_460);
lean_ctor_set_uint8(x_463, sizeof(void*)*10 + 2, x_461);
if (x_1 == 0)
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_464 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_inc(x_2);
x_465 = lean_name_mk_string(x_2, x_464);
x_466 = lean_name_eq(x_3, x_465);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_467 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_inc(x_2);
x_468 = lean_name_mk_string(x_2, x_467);
x_469 = lean_name_eq(x_3, x_468);
lean_dec(x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_470 = l_Lean_mkHole___closed__1;
lean_inc(x_2);
x_471 = lean_name_mk_string(x_2, x_470);
x_472 = lean_name_eq(x_3, x_471);
lean_dec(x_471);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; uint8_t x_475; 
x_473 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
lean_inc(x_2);
x_474 = lean_name_mk_string(x_2, x_473);
x_475 = lean_name_eq(x_3, x_474);
lean_dec(x_474);
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; 
lean_dec(x_6);
x_476 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_inc(x_2);
x_477 = lean_name_mk_string(x_2, x_476);
x_478 = lean_name_eq(x_3, x_477);
lean_dec(x_477);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; 
x_479 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_inc(x_2);
x_480 = lean_name_mk_string(x_2, x_479);
x_481 = lean_name_eq(x_3, x_480);
lean_dec(x_480);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; uint8_t x_484; 
lean_dec(x_5);
x_482 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
x_483 = lean_name_mk_string(x_2, x_482);
x_484 = lean_name_eq(x_3, x_483);
lean_dec(x_483);
if (x_484 == 0)
{
lean_object* x_485; uint8_t x_486; 
x_485 = l_Lean_strLitKind;
x_486 = lean_name_eq(x_3, x_485);
if (x_486 == 0)
{
lean_object* x_487; uint8_t x_488; 
x_487 = l_Lean_numLitKind;
x_488 = lean_name_eq(x_3, x_487);
if (x_488 == 0)
{
lean_object* x_489; uint8_t x_490; 
x_489 = l_Lean_charLitKind;
x_490 = lean_name_eq(x_3, x_489);
if (x_490 == 0)
{
lean_object* x_491; uint8_t x_492; 
lean_dec(x_4);
x_491 = l_Lean_choiceKind;
x_492 = lean_name_eq(x_3, x_491);
lean_dec(x_3);
if (x_492 == 0)
{
lean_object* x_493; 
x_493 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_463, x_9);
lean_dec(x_7);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_7);
x_494 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
x_495 = l_Lean_Elab_Term_throwError___rarg(x_494, x_463, x_9);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_496);
lean_ctor_set(x_499, 1, x_497);
return x_499;
}
}
else
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_463);
lean_dec(x_3);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_4);
lean_ctor_set(x_500, 1, x_7);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_9);
return x_501;
}
}
else
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_463);
lean_dec(x_3);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_4);
lean_ctor_set(x_502, 1, x_7);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_9);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_463);
lean_dec(x_3);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_4);
lean_ctor_set(x_504, 1, x_7);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_9);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_463);
lean_dec(x_3);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_4);
lean_ctor_set(x_506, 1, x_7);
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_9);
return x_507;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
lean_dec(x_3);
lean_dec(x_2);
x_508 = lean_unsigned_to_nat(0u);
x_509 = l_Lean_Syntax_getArg(x_4, x_508);
x_510 = l_Lean_Syntax_getId(x_509);
x_511 = 0;
lean_inc(x_463);
x_512 = l___private_Lean_Elab_Match_15__processVar(x_510, x_511, x_7, x_463, x_9);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = lean_unsigned_to_nat(2u);
x_517 = l_Lean_Syntax_getArg(x_4, x_516);
lean_dec(x_4);
lean_inc(x_463);
x_518 = l___private_Lean_Elab_Match_20__collect___main(x_517, x_515, x_463, x_514);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = lean_ctor_get(x_519, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_523 = x_519;
} else {
 lean_dec_ref(x_519);
 x_523 = lean_box(0);
}
x_524 = l_Lean_Elab_Term_getCurrMacroScope(x_463, x_520);
lean_dec(x_463);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_527 = l_Lean_Elab_Term_getMainModule___rarg(x_526);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_530 = x_527;
} else {
 lean_dec_ref(x_527);
 x_530 = lean_box(0);
}
x_531 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_532 = l_Lean_addMacroScope(x_528, x_531, x_525);
x_533 = l_Lean_SourceInfo_inhabited___closed__1;
x_534 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_535 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_536 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_534);
lean_ctor_set(x_536, 2, x_532);
lean_ctor_set(x_536, 3, x_535);
x_537 = l_Array_empty___closed__1;
x_538 = lean_array_push(x_537, x_536);
x_539 = lean_array_push(x_537, x_509);
x_540 = lean_array_push(x_539, x_521);
x_541 = l_Lean_nullKind___closed__2;
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
x_543 = lean_array_push(x_538, x_542);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_5);
lean_ctor_set(x_544, 1, x_543);
if (lean_is_scalar(x_523)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_523;
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_522);
if (lean_is_scalar(x_530)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_530;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_529);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_509);
lean_dec(x_463);
lean_dec(x_5);
x_547 = lean_ctor_get(x_518, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_518, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_549 = x_518;
} else {
 lean_dec_ref(x_518);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_509);
lean_dec(x_463);
lean_dec(x_5);
lean_dec(x_4);
x_551 = lean_ctor_get(x_512, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_512, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_553 = x_512;
} else {
 lean_dec_ref(x_512);
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
lean_object* x_555; lean_object* x_556; uint8_t x_557; lean_object* x_558; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_555 = lean_unsigned_to_nat(0u);
x_556 = l_Lean_Syntax_getArg(x_4, x_555);
x_557 = 1;
x_558 = l___private_Lean_Elab_Match_16__processIdAux(x_556, x_557, x_7, x_463, x_9);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_561 = x_558;
} else {
 lean_dec_ref(x_558);
 x_561 = lean_box(0);
}
x_562 = lean_ctor_get(x_559, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_563 = x_559;
} else {
 lean_dec_ref(x_559);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_4);
lean_ctor_set(x_564, 1, x_562);
if (lean_is_scalar(x_561)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_561;
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_560);
return x_565;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_4);
x_566 = lean_ctor_get(x_558, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_558, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_568 = x_558;
} else {
 lean_dec_ref(x_558);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
}
else
{
lean_object* x_570; lean_object* x_571; uint8_t x_572; 
lean_dec(x_5);
x_570 = l_Lean_Syntax_inhabited;
x_571 = lean_array_get(x_570, x_6, x_12);
x_572 = l_Lean_Syntax_isNone(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
lean_dec(x_4);
x_573 = lean_unsigned_to_nat(0u);
x_574 = l_Lean_Syntax_getArg(x_571, x_573);
x_575 = l_Lean_Syntax_getArg(x_571, x_12);
x_576 = l_Lean_Syntax_isNone(x_575);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; 
x_577 = l_Lean_Syntax_getArg(x_575, x_573);
x_578 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_579 = lean_name_mk_string(x_2, x_578);
lean_inc(x_577);
x_580 = l_Lean_Syntax_isOfKind(x_577, x_579);
lean_dec(x_579);
if (x_580 == 0)
{
lean_object* x_581; 
lean_inc(x_463);
x_581 = l___private_Lean_Elab_Match_20__collect___main(x_574, x_7, x_463, x_9);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
x_584 = lean_ctor_get(x_582, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_582, 1);
lean_inc(x_585);
lean_dec(x_582);
x_586 = l_Lean_Syntax_setArg(x_571, x_573, x_584);
x_587 = l_Lean_Syntax_getArg(x_577, x_12);
x_588 = l_Lean_Syntax_getArgs(x_587);
lean_dec(x_587);
x_589 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_590 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_588, x_589, x_585, x_463, x_583);
lean_dec(x_588);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_593 = x_590;
} else {
 lean_dec_ref(x_590);
 x_593 = lean_box(0);
}
x_594 = lean_ctor_get(x_591, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_591, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_596 = x_591;
} else {
 lean_dec_ref(x_591);
 x_596 = lean_box(0);
}
x_597 = l_Lean_nullKind;
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_594);
x_599 = l_Lean_Syntax_setArg(x_577, x_12, x_598);
x_600 = l_Lean_Syntax_setArg(x_575, x_573, x_599);
x_601 = l_Lean_Syntax_setArg(x_586, x_12, x_600);
x_602 = lean_array_set(x_6, x_12, x_601);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_3);
lean_ctor_set(x_603, 1, x_602);
if (lean_is_scalar(x_596)) {
 x_604 = lean_alloc_ctor(0, 2, 0);
} else {
 x_604 = x_596;
}
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_595);
if (lean_is_scalar(x_593)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_593;
}
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_592);
return x_605;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_586);
lean_dec(x_577);
lean_dec(x_575);
lean_dec(x_6);
lean_dec(x_3);
x_606 = lean_ctor_get(x_590, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_590, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_608 = x_590;
} else {
 lean_dec_ref(x_590);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_577);
lean_dec(x_575);
lean_dec(x_571);
lean_dec(x_463);
lean_dec(x_6);
lean_dec(x_3);
x_610 = lean_ctor_get(x_581, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_581, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_612 = x_581;
} else {
 lean_dec_ref(x_581);
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
else
{
lean_object* x_614; 
lean_dec(x_577);
lean_dec(x_575);
x_614 = l___private_Lean_Elab_Match_20__collect___main(x_574, x_7, x_463, x_9);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
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
x_618 = lean_ctor_get(x_615, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_615, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_620 = x_615;
} else {
 lean_dec_ref(x_615);
 x_620 = lean_box(0);
}
x_621 = l_Lean_Syntax_setArg(x_571, x_573, x_618);
x_622 = lean_array_set(x_6, x_12, x_621);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_3);
lean_ctor_set(x_623, 1, x_622);
if (lean_is_scalar(x_620)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_620;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_619);
if (lean_is_scalar(x_617)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_617;
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_616);
return x_625;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_571);
lean_dec(x_6);
lean_dec(x_3);
x_626 = lean_ctor_get(x_614, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_614, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_628 = x_614;
} else {
 lean_dec_ref(x_614);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
}
else
{
lean_object* x_630; 
lean_dec(x_575);
lean_dec(x_2);
x_630 = l___private_Lean_Elab_Match_20__collect___main(x_574, x_7, x_463, x_9);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_633 = x_630;
} else {
 lean_dec_ref(x_630);
 x_633 = lean_box(0);
}
x_634 = lean_ctor_get(x_631, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_631, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_636 = x_631;
} else {
 lean_dec_ref(x_631);
 x_636 = lean_box(0);
}
x_637 = l_Lean_Syntax_setArg(x_571, x_573, x_634);
x_638 = lean_array_set(x_6, x_12, x_637);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_3);
lean_ctor_set(x_639, 1, x_638);
if (lean_is_scalar(x_636)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_636;
}
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_635);
if (lean_is_scalar(x_633)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_633;
}
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_632);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_571);
lean_dec(x_6);
lean_dec(x_3);
x_642 = lean_ctor_get(x_630, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_630, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_644 = x_630;
} else {
 lean_dec_ref(x_630);
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
lean_object* x_646; lean_object* x_647; 
lean_dec(x_571);
lean_dec(x_463);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_4);
lean_ctor_set(x_646, 1, x_7);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_9);
return x_647;
}
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_648 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_463, x_9);
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_651 = x_648;
} else {
 lean_dec_ref(x_648);
 x_651 = lean_box(0);
}
x_652 = lean_ctor_get(x_7, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_7, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_654 = x_7;
} else {
 lean_dec_ref(x_7);
 x_654 = lean_box(0);
}
x_655 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_649);
x_656 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_656, 0, x_655);
x_657 = lean_array_push(x_653, x_656);
if (lean_is_scalar(x_654)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_654;
}
lean_ctor_set(x_658, 0, x_652);
lean_ctor_set(x_658, 1, x_657);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_649);
lean_ctor_set(x_659, 1, x_658);
if (lean_is_scalar(x_651)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_651;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_650);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_661 = l_Lean_Syntax_inhabited;
x_662 = lean_array_get(x_661, x_6, x_12);
x_663 = l_Lean_Syntax_isNone(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_664 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
x_665 = l_Lean_Elab_Term_throwErrorAt___rarg(x_662, x_664, x_463, x_9);
lean_dec(x_662);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 x_668 = x_665;
} else {
 lean_dec_ref(x_665);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_662);
x_670 = lean_unsigned_to_nat(2u);
x_671 = lean_array_get(x_661, x_6, x_670);
x_672 = l_Lean_Syntax_getArgs(x_671);
lean_dec(x_671);
x_673 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
x_674 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_672, x_673, x_7, x_463, x_9);
lean_dec(x_672);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
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
x_678 = lean_ctor_get(x_675, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_675, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_680 = x_675;
} else {
 lean_dec_ref(x_675);
 x_680 = lean_box(0);
}
x_681 = l_Lean_nullKind;
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_678);
x_683 = lean_array_set(x_6, x_670, x_682);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_3);
lean_ctor_set(x_684, 1, x_683);
if (lean_is_scalar(x_680)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_680;
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_679);
if (lean_is_scalar(x_677)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_677;
}
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_676);
return x_686;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_6);
lean_dec(x_3);
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_689 = x_674;
} else {
 lean_dec_ref(x_674);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_691 = l_Lean_Syntax_inhabited;
x_692 = lean_array_get(x_691, x_6, x_12);
x_693 = l_Lean_Syntax_getArgs(x_692);
lean_dec(x_692);
x_694 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_695 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_693, x_694, x_7, x_463, x_9);
lean_dec(x_693);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_698 = x_695;
} else {
 lean_dec_ref(x_695);
 x_698 = lean_box(0);
}
x_699 = lean_ctor_get(x_696, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_696, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_701 = x_696;
} else {
 lean_dec_ref(x_696);
 x_701 = lean_box(0);
}
x_702 = l_Lean_nullKind;
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_699);
x_704 = lean_array_set(x_6, x_12, x_703);
x_705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_705, 0, x_3);
lean_ctor_set(x_705, 1, x_704);
if (lean_is_scalar(x_701)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_701;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_700);
if (lean_is_scalar(x_698)) {
 x_707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_707 = x_698;
}
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_697);
return x_707;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_6);
lean_dec(x_3);
x_708 = lean_ctor_get(x_695, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_695, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_710 = x_695;
} else {
 lean_dec_ref(x_695);
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
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_5);
lean_dec(x_4);
x_712 = l_Lean_Syntax_inhabited;
x_713 = lean_unsigned_to_nat(0u);
x_714 = lean_array_get(x_712, x_6, x_713);
x_715 = lean_array_get(x_712, x_6, x_12);
x_716 = l_Lean_Syntax_getArgs(x_715);
lean_dec(x_715);
lean_inc(x_463);
x_717 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_2, x_716, x_713, x_7, x_463, x_9);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = 1;
lean_inc(x_463);
x_722 = l___private_Lean_Elab_Match_16__processIdAux(x_714, x_721, x_720, x_463, x_719);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_725 = lean_ctor_get(x_723, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_723, 1);
lean_inc(x_726);
lean_dec(x_723);
x_727 = x_716;
x_728 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed), 6, 3);
lean_closure_set(x_728, 0, x_725);
lean_closure_set(x_728, 1, x_713);
lean_closure_set(x_728, 2, x_727);
x_729 = x_728;
x_730 = lean_apply_3(x_729, x_726, x_463, x_724);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_733 = x_730;
} else {
 lean_dec_ref(x_730);
 x_733 = lean_box(0);
}
x_734 = lean_ctor_get(x_731, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_731, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_736 = x_731;
} else {
 lean_dec_ref(x_731);
 x_736 = lean_box(0);
}
x_737 = l_Lean_nullKind;
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_734);
x_739 = lean_array_set(x_6, x_12, x_738);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_3);
lean_ctor_set(x_740, 1, x_739);
if (lean_is_scalar(x_736)) {
 x_741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_741 = x_736;
}
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_735);
if (lean_is_scalar(x_733)) {
 x_742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_742 = x_733;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_732);
return x_742;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_6);
lean_dec(x_3);
x_743 = lean_ctor_get(x_730, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_730, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_745 = x_730;
} else {
 lean_dec_ref(x_730);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 2, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_744);
return x_746;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_716);
lean_dec(x_463);
lean_dec(x_6);
lean_dec(x_3);
x_747 = lean_ctor_get(x_722, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_722, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 x_749 = x_722;
} else {
 lean_dec_ref(x_722);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_747);
lean_ctor_set(x_750, 1, x_748);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_716);
lean_dec(x_714);
lean_dec(x_463);
lean_dec(x_6);
lean_dec(x_3);
x_751 = lean_ctor_get(x_717, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_717, 1);
lean_inc(x_752);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_753 = x_717;
} else {
 lean_dec_ref(x_717);
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
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; uint8_t x_772; uint8_t x_773; uint8_t x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_755 = lean_ctor_get(x_9, 0);
x_756 = lean_ctor_get(x_9, 1);
x_757 = lean_ctor_get(x_9, 2);
x_758 = lean_ctor_get(x_9, 3);
x_759 = lean_ctor_get(x_9, 4);
x_760 = lean_ctor_get(x_9, 5);
lean_inc(x_760);
lean_inc(x_759);
lean_inc(x_758);
lean_inc(x_757);
lean_inc(x_756);
lean_inc(x_755);
lean_dec(x_9);
x_761 = lean_unsigned_to_nat(1u);
x_762 = lean_nat_add(x_760, x_761);
x_763 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_763, 0, x_755);
lean_ctor_set(x_763, 1, x_756);
lean_ctor_set(x_763, 2, x_757);
lean_ctor_set(x_763, 3, x_758);
lean_ctor_set(x_763, 4, x_759);
lean_ctor_set(x_763, 5, x_762);
x_764 = lean_ctor_get(x_8, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_8, 1);
lean_inc(x_765);
x_766 = lean_ctor_get(x_8, 2);
lean_inc(x_766);
x_767 = lean_ctor_get(x_8, 3);
lean_inc(x_767);
x_768 = lean_ctor_get(x_8, 4);
lean_inc(x_768);
x_769 = lean_ctor_get(x_8, 5);
lean_inc(x_769);
x_770 = lean_ctor_get(x_8, 6);
lean_inc(x_770);
x_771 = lean_ctor_get(x_8, 7);
lean_inc(x_771);
x_772 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_773 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_774 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_775 = lean_ctor_get(x_8, 9);
lean_inc(x_775);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 lean_ctor_release(x_8, 6);
 lean_ctor_release(x_8, 7);
 lean_ctor_release(x_8, 8);
 lean_ctor_release(x_8, 9);
 x_776 = x_8;
} else {
 lean_dec_ref(x_8);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(0, 10, 3);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_764);
lean_ctor_set(x_777, 1, x_765);
lean_ctor_set(x_777, 2, x_766);
lean_ctor_set(x_777, 3, x_767);
lean_ctor_set(x_777, 4, x_768);
lean_ctor_set(x_777, 5, x_769);
lean_ctor_set(x_777, 6, x_770);
lean_ctor_set(x_777, 7, x_771);
lean_ctor_set(x_777, 8, x_760);
lean_ctor_set(x_777, 9, x_775);
lean_ctor_set_uint8(x_777, sizeof(void*)*10, x_772);
lean_ctor_set_uint8(x_777, sizeof(void*)*10 + 1, x_773);
lean_ctor_set_uint8(x_777, sizeof(void*)*10 + 2, x_774);
if (x_1 == 0)
{
lean_object* x_778; lean_object* x_779; uint8_t x_780; 
x_778 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_inc(x_2);
x_779 = lean_name_mk_string(x_2, x_778);
x_780 = lean_name_eq(x_3, x_779);
lean_dec(x_779);
if (x_780 == 0)
{
lean_object* x_781; lean_object* x_782; uint8_t x_783; 
x_781 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_inc(x_2);
x_782 = lean_name_mk_string(x_2, x_781);
x_783 = lean_name_eq(x_3, x_782);
lean_dec(x_782);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; uint8_t x_786; 
x_784 = l_Lean_mkHole___closed__1;
lean_inc(x_2);
x_785 = lean_name_mk_string(x_2, x_784);
x_786 = lean_name_eq(x_3, x_785);
lean_dec(x_785);
if (x_786 == 0)
{
lean_object* x_787; lean_object* x_788; uint8_t x_789; 
x_787 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
lean_inc(x_2);
x_788 = lean_name_mk_string(x_2, x_787);
x_789 = lean_name_eq(x_3, x_788);
lean_dec(x_788);
if (x_789 == 0)
{
lean_object* x_790; lean_object* x_791; uint8_t x_792; 
lean_dec(x_6);
x_790 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_inc(x_2);
x_791 = lean_name_mk_string(x_2, x_790);
x_792 = lean_name_eq(x_3, x_791);
lean_dec(x_791);
if (x_792 == 0)
{
lean_object* x_793; lean_object* x_794; uint8_t x_795; 
x_793 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_inc(x_2);
x_794 = lean_name_mk_string(x_2, x_793);
x_795 = lean_name_eq(x_3, x_794);
lean_dec(x_794);
if (x_795 == 0)
{
lean_object* x_796; lean_object* x_797; uint8_t x_798; 
lean_dec(x_5);
x_796 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
x_797 = lean_name_mk_string(x_2, x_796);
x_798 = lean_name_eq(x_3, x_797);
lean_dec(x_797);
if (x_798 == 0)
{
lean_object* x_799; uint8_t x_800; 
x_799 = l_Lean_strLitKind;
x_800 = lean_name_eq(x_3, x_799);
if (x_800 == 0)
{
lean_object* x_801; uint8_t x_802; 
x_801 = l_Lean_numLitKind;
x_802 = lean_name_eq(x_3, x_801);
if (x_802 == 0)
{
lean_object* x_803; uint8_t x_804; 
x_803 = l_Lean_charLitKind;
x_804 = lean_name_eq(x_3, x_803);
if (x_804 == 0)
{
lean_object* x_805; uint8_t x_806; 
lean_dec(x_4);
x_805 = l_Lean_choiceKind;
x_806 = lean_name_eq(x_3, x_805);
lean_dec(x_3);
if (x_806 == 0)
{
lean_object* x_807; 
x_807 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_777, x_763);
lean_dec(x_7);
return x_807;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_7);
x_808 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
x_809 = l_Lean_Elab_Term_throwError___rarg(x_808, x_777, x_763);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 x_812 = x_809;
} else {
 lean_dec_ref(x_809);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(1, 2, 0);
} else {
 x_813 = x_812;
}
lean_ctor_set(x_813, 0, x_810);
lean_ctor_set(x_813, 1, x_811);
return x_813;
}
}
else
{
lean_object* x_814; lean_object* x_815; 
lean_dec(x_777);
lean_dec(x_3);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_4);
lean_ctor_set(x_814, 1, x_7);
x_815 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_763);
return x_815;
}
}
else
{
lean_object* x_816; lean_object* x_817; 
lean_dec(x_777);
lean_dec(x_3);
x_816 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_816, 0, x_4);
lean_ctor_set(x_816, 1, x_7);
x_817 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_763);
return x_817;
}
}
else
{
lean_object* x_818; lean_object* x_819; 
lean_dec(x_777);
lean_dec(x_3);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_4);
lean_ctor_set(x_818, 1, x_7);
x_819 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_763);
return x_819;
}
}
else
{
lean_object* x_820; lean_object* x_821; 
lean_dec(x_777);
lean_dec(x_3);
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_4);
lean_ctor_set(x_820, 1, x_7);
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_820);
lean_ctor_set(x_821, 1, x_763);
return x_821;
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; uint8_t x_825; lean_object* x_826; 
lean_dec(x_3);
lean_dec(x_2);
x_822 = lean_unsigned_to_nat(0u);
x_823 = l_Lean_Syntax_getArg(x_4, x_822);
x_824 = l_Lean_Syntax_getId(x_823);
x_825 = 0;
lean_inc(x_777);
x_826 = l___private_Lean_Elab_Match_15__processVar(x_824, x_825, x_7, x_777, x_763);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
x_830 = lean_unsigned_to_nat(2u);
x_831 = l_Lean_Syntax_getArg(x_4, x_830);
lean_dec(x_4);
lean_inc(x_777);
x_832 = l___private_Lean_Elab_Match_20__collect___main(x_831, x_829, x_777, x_828);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_ctor_get(x_833, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_833, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_837 = x_833;
} else {
 lean_dec_ref(x_833);
 x_837 = lean_box(0);
}
x_838 = l_Lean_Elab_Term_getCurrMacroScope(x_777, x_834);
lean_dec(x_777);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
lean_dec(x_838);
x_841 = l_Lean_Elab_Term_getMainModule___rarg(x_840);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_844 = x_841;
} else {
 lean_dec_ref(x_841);
 x_844 = lean_box(0);
}
x_845 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_846 = l_Lean_addMacroScope(x_842, x_845, x_839);
x_847 = l_Lean_SourceInfo_inhabited___closed__1;
x_848 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_849 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_850 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_850, 0, x_847);
lean_ctor_set(x_850, 1, x_848);
lean_ctor_set(x_850, 2, x_846);
lean_ctor_set(x_850, 3, x_849);
x_851 = l_Array_empty___closed__1;
x_852 = lean_array_push(x_851, x_850);
x_853 = lean_array_push(x_851, x_823);
x_854 = lean_array_push(x_853, x_835);
x_855 = l_Lean_nullKind___closed__2;
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_854);
x_857 = lean_array_push(x_852, x_856);
x_858 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_858, 0, x_5);
lean_ctor_set(x_858, 1, x_857);
if (lean_is_scalar(x_837)) {
 x_859 = lean_alloc_ctor(0, 2, 0);
} else {
 x_859 = x_837;
}
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_836);
if (lean_is_scalar(x_844)) {
 x_860 = lean_alloc_ctor(0, 2, 0);
} else {
 x_860 = x_844;
}
lean_ctor_set(x_860, 0, x_859);
lean_ctor_set(x_860, 1, x_843);
return x_860;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
lean_dec(x_823);
lean_dec(x_777);
lean_dec(x_5);
x_861 = lean_ctor_get(x_832, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_832, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_863 = x_832;
} else {
 lean_dec_ref(x_832);
 x_863 = lean_box(0);
}
if (lean_is_scalar(x_863)) {
 x_864 = lean_alloc_ctor(1, 2, 0);
} else {
 x_864 = x_863;
}
lean_ctor_set(x_864, 0, x_861);
lean_ctor_set(x_864, 1, x_862);
return x_864;
}
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_823);
lean_dec(x_777);
lean_dec(x_5);
lean_dec(x_4);
x_865 = lean_ctor_get(x_826, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_826, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_867 = x_826;
} else {
 lean_dec_ref(x_826);
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
lean_object* x_869; lean_object* x_870; uint8_t x_871; lean_object* x_872; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_869 = lean_unsigned_to_nat(0u);
x_870 = l_Lean_Syntax_getArg(x_4, x_869);
x_871 = 1;
x_872 = l___private_Lean_Elab_Match_16__processIdAux(x_870, x_871, x_7, x_777, x_763);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_875 = x_872;
} else {
 lean_dec_ref(x_872);
 x_875 = lean_box(0);
}
x_876 = lean_ctor_get(x_873, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_877 = x_873;
} else {
 lean_dec_ref(x_873);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_4);
lean_ctor_set(x_878, 1, x_876);
if (lean_is_scalar(x_875)) {
 x_879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_879 = x_875;
}
lean_ctor_set(x_879, 0, x_878);
lean_ctor_set(x_879, 1, x_874);
return x_879;
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_4);
x_880 = lean_ctor_get(x_872, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_872, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_882 = x_872;
} else {
 lean_dec_ref(x_872);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
}
else
{
lean_object* x_884; lean_object* x_885; uint8_t x_886; 
lean_dec(x_5);
x_884 = l_Lean_Syntax_inhabited;
x_885 = lean_array_get(x_884, x_6, x_761);
x_886 = l_Lean_Syntax_isNone(x_885);
if (x_886 == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; uint8_t x_890; 
lean_dec(x_4);
x_887 = lean_unsigned_to_nat(0u);
x_888 = l_Lean_Syntax_getArg(x_885, x_887);
x_889 = l_Lean_Syntax_getArg(x_885, x_761);
x_890 = l_Lean_Syntax_isNone(x_889);
if (x_890 == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; 
x_891 = l_Lean_Syntax_getArg(x_889, x_887);
x_892 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_893 = lean_name_mk_string(x_2, x_892);
lean_inc(x_891);
x_894 = l_Lean_Syntax_isOfKind(x_891, x_893);
lean_dec(x_893);
if (x_894 == 0)
{
lean_object* x_895; 
lean_inc(x_777);
x_895 = l___private_Lean_Elab_Match_20__collect___main(x_888, x_7, x_777, x_763);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_895, 1);
lean_inc(x_897);
lean_dec(x_895);
x_898 = lean_ctor_get(x_896, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_896, 1);
lean_inc(x_899);
lean_dec(x_896);
x_900 = l_Lean_Syntax_setArg(x_885, x_887, x_898);
x_901 = l_Lean_Syntax_getArg(x_891, x_761);
x_902 = l_Lean_Syntax_getArgs(x_901);
lean_dec(x_901);
x_903 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_904 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_902, x_903, x_899, x_777, x_897);
lean_dec(x_902);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_907 = x_904;
} else {
 lean_dec_ref(x_904);
 x_907 = lean_box(0);
}
x_908 = lean_ctor_get(x_905, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_905, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_910 = x_905;
} else {
 lean_dec_ref(x_905);
 x_910 = lean_box(0);
}
x_911 = l_Lean_nullKind;
x_912 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_912, 0, x_911);
lean_ctor_set(x_912, 1, x_908);
x_913 = l_Lean_Syntax_setArg(x_891, x_761, x_912);
x_914 = l_Lean_Syntax_setArg(x_889, x_887, x_913);
x_915 = l_Lean_Syntax_setArg(x_900, x_761, x_914);
x_916 = lean_array_set(x_6, x_761, x_915);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_3);
lean_ctor_set(x_917, 1, x_916);
if (lean_is_scalar(x_910)) {
 x_918 = lean_alloc_ctor(0, 2, 0);
} else {
 x_918 = x_910;
}
lean_ctor_set(x_918, 0, x_917);
lean_ctor_set(x_918, 1, x_909);
if (lean_is_scalar(x_907)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_907;
}
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_906);
return x_919;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
lean_dec(x_900);
lean_dec(x_891);
lean_dec(x_889);
lean_dec(x_6);
lean_dec(x_3);
x_920 = lean_ctor_get(x_904, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_904, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_922 = x_904;
} else {
 lean_dec_ref(x_904);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_920);
lean_ctor_set(x_923, 1, x_921);
return x_923;
}
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_dec(x_891);
lean_dec(x_889);
lean_dec(x_885);
lean_dec(x_777);
lean_dec(x_6);
lean_dec(x_3);
x_924 = lean_ctor_get(x_895, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_895, 1);
lean_inc(x_925);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 lean_ctor_release(x_895, 1);
 x_926 = x_895;
} else {
 lean_dec_ref(x_895);
 x_926 = lean_box(0);
}
if (lean_is_scalar(x_926)) {
 x_927 = lean_alloc_ctor(1, 2, 0);
} else {
 x_927 = x_926;
}
lean_ctor_set(x_927, 0, x_924);
lean_ctor_set(x_927, 1, x_925);
return x_927;
}
}
else
{
lean_object* x_928; 
lean_dec(x_891);
lean_dec(x_889);
x_928 = l___private_Lean_Elab_Match_20__collect___main(x_888, x_7, x_777, x_763);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_931 = x_928;
} else {
 lean_dec_ref(x_928);
 x_931 = lean_box(0);
}
x_932 = lean_ctor_get(x_929, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_929, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_934 = x_929;
} else {
 lean_dec_ref(x_929);
 x_934 = lean_box(0);
}
x_935 = l_Lean_Syntax_setArg(x_885, x_887, x_932);
x_936 = lean_array_set(x_6, x_761, x_935);
x_937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_937, 0, x_3);
lean_ctor_set(x_937, 1, x_936);
if (lean_is_scalar(x_934)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_934;
}
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_933);
if (lean_is_scalar(x_931)) {
 x_939 = lean_alloc_ctor(0, 2, 0);
} else {
 x_939 = x_931;
}
lean_ctor_set(x_939, 0, x_938);
lean_ctor_set(x_939, 1, x_930);
return x_939;
}
else
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
lean_dec(x_885);
lean_dec(x_6);
lean_dec(x_3);
x_940 = lean_ctor_get(x_928, 0);
lean_inc(x_940);
x_941 = lean_ctor_get(x_928, 1);
lean_inc(x_941);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_942 = x_928;
} else {
 lean_dec_ref(x_928);
 x_942 = lean_box(0);
}
if (lean_is_scalar(x_942)) {
 x_943 = lean_alloc_ctor(1, 2, 0);
} else {
 x_943 = x_942;
}
lean_ctor_set(x_943, 0, x_940);
lean_ctor_set(x_943, 1, x_941);
return x_943;
}
}
}
else
{
lean_object* x_944; 
lean_dec(x_889);
lean_dec(x_2);
x_944 = l___private_Lean_Elab_Match_20__collect___main(x_888, x_7, x_777, x_763);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 lean_ctor_release(x_944, 1);
 x_947 = x_944;
} else {
 lean_dec_ref(x_944);
 x_947 = lean_box(0);
}
x_948 = lean_ctor_get(x_945, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_945, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_950 = x_945;
} else {
 lean_dec_ref(x_945);
 x_950 = lean_box(0);
}
x_951 = l_Lean_Syntax_setArg(x_885, x_887, x_948);
x_952 = lean_array_set(x_6, x_761, x_951);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_3);
lean_ctor_set(x_953, 1, x_952);
if (lean_is_scalar(x_950)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_950;
}
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_949);
if (lean_is_scalar(x_947)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_947;
}
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_946);
return x_955;
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
lean_dec(x_885);
lean_dec(x_6);
lean_dec(x_3);
x_956 = lean_ctor_get(x_944, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_944, 1);
lean_inc(x_957);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 lean_ctor_release(x_944, 1);
 x_958 = x_944;
} else {
 lean_dec_ref(x_944);
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
lean_object* x_960; lean_object* x_961; 
lean_dec(x_885);
lean_dec(x_777);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_4);
lean_ctor_set(x_960, 1, x_7);
x_961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_961, 0, x_960);
lean_ctor_set(x_961, 1, x_763);
return x_961;
}
}
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_962 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_777, x_763);
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
x_966 = lean_ctor_get(x_7, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_7, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_968 = x_7;
} else {
 lean_dec_ref(x_7);
 x_968 = lean_box(0);
}
x_969 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_963);
x_970 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_970, 0, x_969);
x_971 = lean_array_push(x_967, x_970);
if (lean_is_scalar(x_968)) {
 x_972 = lean_alloc_ctor(0, 2, 0);
} else {
 x_972 = x_968;
}
lean_ctor_set(x_972, 0, x_966);
lean_ctor_set(x_972, 1, x_971);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_963);
lean_ctor_set(x_973, 1, x_972);
if (lean_is_scalar(x_965)) {
 x_974 = lean_alloc_ctor(0, 2, 0);
} else {
 x_974 = x_965;
}
lean_ctor_set(x_974, 0, x_973);
lean_ctor_set(x_974, 1, x_964);
return x_974;
}
}
else
{
lean_object* x_975; lean_object* x_976; uint8_t x_977; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_975 = l_Lean_Syntax_inhabited;
x_976 = lean_array_get(x_975, x_6, x_761);
x_977 = l_Lean_Syntax_isNone(x_976);
if (x_977 == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_978 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
x_979 = l_Lean_Elab_Term_throwErrorAt___rarg(x_976, x_978, x_777, x_763);
lean_dec(x_976);
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_979, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_982 = x_979;
} else {
 lean_dec_ref(x_979);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_980);
lean_ctor_set(x_983, 1, x_981);
return x_983;
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_976);
x_984 = lean_unsigned_to_nat(2u);
x_985 = lean_array_get(x_975, x_6, x_984);
x_986 = l_Lean_Syntax_getArgs(x_985);
lean_dec(x_985);
x_987 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
x_988 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_986, x_987, x_7, x_777, x_763);
lean_dec(x_986);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_991 = x_988;
} else {
 lean_dec_ref(x_988);
 x_991 = lean_box(0);
}
x_992 = lean_ctor_get(x_989, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_989, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 x_994 = x_989;
} else {
 lean_dec_ref(x_989);
 x_994 = lean_box(0);
}
x_995 = l_Lean_nullKind;
x_996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_996, 0, x_995);
lean_ctor_set(x_996, 1, x_992);
x_997 = lean_array_set(x_6, x_984, x_996);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_3);
lean_ctor_set(x_998, 1, x_997);
if (lean_is_scalar(x_994)) {
 x_999 = lean_alloc_ctor(0, 2, 0);
} else {
 x_999 = x_994;
}
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_993);
if (lean_is_scalar(x_991)) {
 x_1000 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1000 = x_991;
}
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_990);
return x_1000;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_6);
lean_dec(x_3);
x_1001 = lean_ctor_get(x_988, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_988, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_1003 = x_988;
} else {
 lean_dec_ref(x_988);
 x_1003 = lean_box(0);
}
if (lean_is_scalar(x_1003)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_1003;
}
lean_ctor_set(x_1004, 0, x_1001);
lean_ctor_set(x_1004, 1, x_1002);
return x_1004;
}
}
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1005 = l_Lean_Syntax_inhabited;
x_1006 = lean_array_get(x_1005, x_6, x_761);
x_1007 = l_Lean_Syntax_getArgs(x_1006);
lean_dec(x_1006);
x_1008 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_1009 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1007, x_1008, x_7, x_777, x_763);
lean_dec(x_1007);
if (lean_obj_tag(x_1009) == 0)
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1012 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1012 = lean_box(0);
}
x_1013 = lean_ctor_get(x_1010, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1010, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1015 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1015 = lean_box(0);
}
x_1016 = l_Lean_nullKind;
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1013);
x_1018 = lean_array_set(x_6, x_761, x_1017);
x_1019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1019, 0, x_3);
lean_ctor_set(x_1019, 1, x_1018);
if (lean_is_scalar(x_1015)) {
 x_1020 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1020 = x_1015;
}
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_1014);
if (lean_is_scalar(x_1012)) {
 x_1021 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1021 = x_1012;
}
lean_ctor_set(x_1021, 0, x_1020);
lean_ctor_set(x_1021, 1, x_1011);
return x_1021;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_6);
lean_dec(x_3);
x_1022 = lean_ctor_get(x_1009, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1009, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1024 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1024 = lean_box(0);
}
if (lean_is_scalar(x_1024)) {
 x_1025 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1025 = x_1024;
}
lean_ctor_set(x_1025, 0, x_1022);
lean_ctor_set(x_1025, 1, x_1023);
return x_1025;
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_5);
lean_dec(x_4);
x_1026 = l_Lean_Syntax_inhabited;
x_1027 = lean_unsigned_to_nat(0u);
x_1028 = lean_array_get(x_1026, x_6, x_1027);
x_1029 = lean_array_get(x_1026, x_6, x_761);
x_1030 = l_Lean_Syntax_getArgs(x_1029);
lean_dec(x_1029);
lean_inc(x_777);
x_1031 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_2, x_1030, x_1027, x_7, x_777, x_763);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; lean_object* x_1036; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1035 = 1;
lean_inc(x_777);
x_1036 = l___private_Lean_Elab_Match_16__processIdAux(x_1028, x_1035, x_1034, x_777, x_1033);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec(x_1036);
x_1039 = lean_ctor_get(x_1037, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1037, 1);
lean_inc(x_1040);
lean_dec(x_1037);
x_1041 = x_1030;
x_1042 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed), 6, 3);
lean_closure_set(x_1042, 0, x_1039);
lean_closure_set(x_1042, 1, x_1027);
lean_closure_set(x_1042, 2, x_1041);
x_1043 = x_1042;
x_1044 = lean_apply_3(x_1043, x_1040, x_777, x_1038);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1047 = x_1044;
} else {
 lean_dec_ref(x_1044);
 x_1047 = lean_box(0);
}
x_1048 = lean_ctor_get(x_1045, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1045, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1050 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1050 = lean_box(0);
}
x_1051 = l_Lean_nullKind;
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1048);
x_1053 = lean_array_set(x_6, x_761, x_1052);
x_1054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1054, 0, x_3);
lean_ctor_set(x_1054, 1, x_1053);
if (lean_is_scalar(x_1050)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1050;
}
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1049);
if (lean_is_scalar(x_1047)) {
 x_1056 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1056 = x_1047;
}
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1046);
return x_1056;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_6);
lean_dec(x_3);
x_1057 = lean_ctor_get(x_1044, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1044, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1059 = x_1044;
} else {
 lean_dec_ref(x_1044);
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
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
lean_dec(x_1030);
lean_dec(x_777);
lean_dec(x_6);
lean_dec(x_3);
x_1061 = lean_ctor_get(x_1036, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1036, 1);
lean_inc(x_1062);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1063 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1063 = lean_box(0);
}
if (lean_is_scalar(x_1063)) {
 x_1064 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1064 = x_1063;
}
lean_ctor_set(x_1064, 0, x_1061);
lean_ctor_set(x_1064, 1, x_1062);
return x_1064;
}
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_1030);
lean_dec(x_1028);
lean_dec(x_777);
lean_dec(x_6);
lean_dec(x_3);
x_1065 = lean_ctor_get(x_1031, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1031, 1);
lean_inc(x_1066);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1067 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1067 = lean_box(0);
}
if (lean_is_scalar(x_1067)) {
 x_1068 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1068 = x_1067;
}
lean_ctor_set(x_1068, 0, x_1065);
lean_ctor_set(x_1068, 1, x_1066);
return x_1068;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_20__collect___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_mkAppStx___closed__8;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = 0;
x_10 = l_Lean_mkAppStx___closed__6;
x_11 = lean_box(x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_20__collect___main___lambda__2___boxed), 9, 6);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_7);
lean_closure_set(x_12, 5, x_6);
x_13 = l_Lean_Elab_Term_CollectPatternVars_withRef___rarg(x_1, x_12, x_2, x_3, x_4);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = 1;
x_15 = l_Lean_mkAppStx___closed__6;
x_16 = lean_box(x_14);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_20__collect___main___lambda__2___boxed), 9, 6);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_7);
lean_closure_set(x_17, 5, x_6);
x_18 = l_Lean_Elab_Term_CollectPatternVars_withRef___rarg(x_1, x_17, x_2, x_3, x_4);
return x_18;
}
}
case 3:
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = l___private_Lean_Elab_Match_18__processId(x_1, x_2, x_3, x_4);
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
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_1);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
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
default: 
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_2, x_3, x_4);
lean_dec(x_2);
return x_36;
}
}
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Lean_Elab_Match_20__collect___main___lambda__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Match_20__collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_20__collect___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("collecting variables at pattern: ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_array_fget(x_2, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = x_11;
x_15 = l_Lean_Elab_Term_getOptions(x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_19 = l_Lean_checkTraceOption(x_16, x_18);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_4);
x_20 = l___private_Lean_Elab_Match_20__collect___main(x_14, x_3, x_4, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
x_27 = x_23;
x_28 = lean_array_fset(x_13, x_1, x_27);
lean_dec(x_1);
x_1 = x_26;
x_2 = x_28;
x_3 = x_24;
x_5 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_14);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_14);
x_35 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_Term_logTrace(x_18, x_36, x_4, x_17);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_4);
x_39 = l___private_Lean_Elab_Match_20__collect___main(x_14, x_3, x_4, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_1, x_44);
x_46 = x_42;
x_47 = lean_array_fset(x_13, x_1, x_46);
lean_dec(x_1);
x_1 = x_45;
x_2 = x_47;
x_3 = x_43;
x_5 = x_41;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
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
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = x_7;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = x_11;
x_13 = lean_apply_3(x_12, x_2, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
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
lean_ctor_set(x_1, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_1);
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
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
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
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_35 = x_33;
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1), 5, 2);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_35);
x_38 = x_37;
x_39 = lean_apply_3(x_38, x_2, x_3, x_4);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_34);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_34);
lean_dec(x_32);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_51 = x_39;
} else {
 lean_dec_ref(x_39);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
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
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Match_21__collectPatternVars___closed__1;
x_5 = l_Lean_Elab_Term_CollectPatternVars_main(x_1, x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 1, x_9);
lean_ctor_set(x_7, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_mkFVar(x_11);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_inferType(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = 0;
x_18 = lean_box(0);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_mkFreshExprMVarWithId(x_10, x_16, x_17, x_18, x_3, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
x_4 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
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
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_2 = x_29;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = l_Lean_Expr_fvarId_x21(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_array_push(x_2, x_11);
x_13 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_3, x_4, x_9, x_12, x_6, x_7);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = l_Lean_Expr_fvarId_x21(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_push(x_3, x_12);
x_14 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_4, x_5, x_10, x_13, x_7, x_8);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(x_4, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_3(x_2, x_4, x_5, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_mkFreshTypeMVar(x_19, x_20, x_5, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed), 7, 4);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_2);
x_25 = 0;
x_26 = l_Lean_Elab_Term_withLocalDecl___rarg(x_18, x_25, x_22, x_24, x_5, x_23);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = 0;
x_29 = lean_box(0);
lean_inc(x_5);
x_30 = l_Lean_Elab_Term_mkFreshTypeMVar(x_28, x_29, x_5, x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_inc(x_3);
x_34 = l_Lean_Name_appendIndexAfter(x_33, x_3);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed), 8, 5);
lean_closure_set(x_35, 0, x_3);
lean_closure_set(x_35, 1, x_27);
lean_closure_set(x_35, 2, x_4);
lean_closure_set(x_35, 3, x_1);
lean_closure_set(x_35, 4, x_2);
x_36 = 0;
x_37 = l_Lean_Elab_Term_withLocalDecl___rarg(x_34, x_36, x_31, x_35, x_5, x_32);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_23__withPatternVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_23__withPatternVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_23__withPatternVars___rarg), 4, 0);
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
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_whnf(x_3, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_fget(x_1, x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
lean_inc(x_5);
x_18 = l_Lean_Elab_Term_elabTermEnsuringType(x_16, x_17, x_5, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_23 = lean_expr_instantiate1(x_15, x_19);
lean_dec(x_15);
x_24 = lean_array_push(x_4, x_19);
x_2 = x_22;
x_3 = x_23;
x_4 = x_24;
x_6 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3;
x_32 = l_Lean_Elab_Term_throwError___rarg(x_31, x_5, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_24__elabPatternsAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_24__elabPatternsAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_24__elabPatternsAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalizePatternDecls: mvarId: ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fvarId: ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_50 = l_Lean_mkMVar(x_13);
lean_inc(x_5);
lean_inc(x_50);
x_51 = l_Lean_Elab_Term_instantiateMVars(x_50, x_5, x_6);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_76 = l_Lean_Elab_Term_getOptions(x_5, x_53);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_80 = l_Lean_checkTraceOption(x_77, x_79);
lean_dec(x_77);
if (x_80 == 0)
{
lean_dec(x_50);
x_54 = x_78;
goto block_75;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_50);
x_82 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6;
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_52);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_52);
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__9;
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_14);
x_90 = l_Lean_mkFVar(x_14);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Elab_Term_logTrace(x_79, x_92, x_5, x_78);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_54 = x_94;
goto block_75;
}
block_49:
{
lean_object* x_16; 
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_getLocalDecl(x_14, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_18, 4);
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
x_23 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_18, 4, x_23);
x_24 = l_Lean_Meta_instantiateLocalDeclMVars(x_19, x_22, x_18);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_5);
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_17, x_26, x_21);
x_28 = lean_array_push(x_4, x_25);
x_3 = x_12;
x_4 = x_28;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
x_37 = l_Lean_TraceState_Inhabited___closed__1;
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_35);
x_39 = l_Lean_Meta_instantiateLocalDeclMVars(x_19, x_36, x_38);
lean_dec(x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_5);
x_42 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_17, x_41, x_34);
x_43 = lean_array_push(x_4, x_40);
x_3 = x_12;
x_4 = x_43;
x_6 = x_42;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
return x_16;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_16, 0);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_16);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_75:
{
if (lean_obj_tag(x_52) == 2)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
lean_inc(x_14);
x_56 = l_Lean_mkFVar(x_14);
lean_inc(x_56);
lean_inc(x_55);
x_57 = l_Lean_Elab_Term_assignExprMVar(x_55, x_56, x_5, x_54);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Elab_Term_getOptions(x_5, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_63 = l_Lean_checkTraceOption(x_60, x_62);
lean_dec(x_60);
if (x_63 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
x_15 = x_61;
goto block_49;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = l_Lean_mkMVar(x_55);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_56);
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_Term_logTrace(x_62, x_71, x_5, x_61);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_15 = x_73;
goto block_49;
}
}
else
{
lean_dec(x_52);
lean_dec(x_14);
x_3 = x_12;
x_6 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_10, 0);
lean_inc(x_95);
lean_dec(x_10);
lean_inc(x_5);
x_96 = l_Lean_Elab_Term_getLocalDecl(x_95, x_5, x_6);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
lean_dec(x_96);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_98, 4);
x_102 = lean_ctor_get(x_5, 0);
lean_inc(x_102);
x_103 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_98, 4, x_103);
x_104 = l_Lean_Meta_instantiateLocalDeclMVars(x_99, x_102, x_98);
lean_dec(x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_5);
x_107 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_97, x_106, x_101);
x_108 = lean_array_push(x_4, x_105);
x_3 = x_12;
x_4 = x_108;
x_6 = x_107;
goto _start;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_110 = lean_ctor_get(x_98, 0);
x_111 = lean_ctor_get(x_98, 1);
x_112 = lean_ctor_get(x_98, 2);
x_113 = lean_ctor_get(x_98, 3);
x_114 = lean_ctor_get(x_98, 4);
x_115 = lean_ctor_get(x_98, 5);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_98);
x_116 = lean_ctor_get(x_5, 0);
lean_inc(x_116);
x_117 = l_Lean_TraceState_Inhabited___closed__1;
x_118 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_111);
lean_ctor_set(x_118, 2, x_112);
lean_ctor_set(x_118, 3, x_113);
lean_ctor_set(x_118, 4, x_117);
lean_ctor_set(x_118, 5, x_115);
x_119 = l_Lean_Meta_instantiateLocalDeclMVars(x_99, x_116, x_118);
lean_dec(x_116);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_5);
x_122 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_97, x_121, x_114);
x_123 = lean_array_push(x_4, x_120);
x_3 = x_12;
x_4 = x_123;
x_6 = x_122;
goto _start;
}
}
else
{
uint8_t x_125; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_125 = !lean_is_exclusive(x_96);
if (x_125 == 0)
{
return x_96;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_96, 0);
x_127 = lean_ctor_get(x_96, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_96);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_finalizePatternDecls(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_NameSet_contains(x_5, x_1);
lean_dec(x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_25__alreadyVisited(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_26__markAsVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_box(0);
x_8 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_1, x_7);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_11, x_1, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_Match_26__markAsVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_26__markAsVisited(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_indentExpr(x_5);
x_7 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_Term_throwError___rarg(x_8, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Match_29__mkLocalDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Expr_mvarId_x21(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 4);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_8);
lean_ctor_set(x_6, 4, x_10);
lean_inc(x_5);
x_11 = lean_metavar_ctx_get_expr_assignment(x_8, x_5);
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_6, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_mkFreshId(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Elab_Term_inferType(x_1, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
x_19 = l_Lean_mkFVar(x_14);
x_20 = l_Lean_Elab_Term_assignExprMVar(x_5, x_19, x_3, x_18);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_array_get_size(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
x_29 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
x_30 = l_Lean_Name_appendIndexAfter(x_29, x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = 0;
lean_inc(x_14);
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_17);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_34 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_1, x_24, x_31);
lean_dec(x_1);
x_35 = lean_box(0);
lean_inc(x_14);
x_36 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_25, x_14, x_35);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_array_push(x_24, x_33);
lean_ctor_set(x_2, 2, x_36);
lean_ctor_set(x_2, 1, x_37);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_14);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_20, 0, x_39);
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = l_Array_insertAt___rarg(x_24, x_40, x_33);
lean_dec(x_40);
lean_ctor_set(x_2, 2, x_36);
lean_ctor_set(x_2, 1, x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_14);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_20, 0, x_43);
return x_20;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_47);
x_50 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
x_51 = l_Lean_Name_appendIndexAfter(x_50, x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = 0;
lean_inc(x_14);
x_54 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_14);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_17);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_1, x_45, x_52);
lean_dec(x_1);
x_56 = lean_box(0);
lean_inc(x_14);
x_57 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_14, x_56);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_array_push(x_45, x_54);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_14);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_20, 0, x_61);
return x_20;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
lean_dec(x_55);
x_63 = l_Array_insertAt___rarg(x_45, x_62, x_54);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_44);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_57);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_14);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_20, 0, x_66);
return x_20;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_dec(x_20);
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_71 = x_2;
} else {
 lean_dec_ref(x_2);
 x_71 = lean_box(0);
}
x_72 = lean_array_get_size(x_69);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_72, x_73);
lean_dec(x_72);
x_75 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
x_76 = l_Lean_Name_appendIndexAfter(x_75, x_74);
x_77 = lean_unsigned_to_nat(0u);
x_78 = 0;
lean_inc(x_14);
x_79 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_14);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_17);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
x_80 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_1, x_69, x_77);
lean_dec(x_1);
x_81 = lean_box(0);
lean_inc(x_14);
x_82 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_70, x_14, x_81);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_array_push(x_69, x_79);
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(0, 3, 0);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_68);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_14);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_67);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_80, 0);
lean_inc(x_88);
lean_dec(x_80);
x_89 = l_Array_insertAt___rarg(x_69, x_88, x_79);
lean_dec(x_88);
if (lean_is_scalar(x_71)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_71;
}
lean_ctor_set(x_90, 0, x_68);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_82);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_14);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_67);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_16);
if (x_94 == 0)
{
return x_16;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_16, 0);
x_96 = lean_ctor_get(x_16, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_16);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_ctor_get(x_11, 0);
lean_inc(x_98);
lean_dec(x_11);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_12);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_105 = lean_ctor_get(x_6, 3);
x_106 = lean_ctor_get(x_6, 4);
x_107 = lean_ctor_get(x_6, 5);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_108 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_103);
x_109 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_104);
lean_ctor_set(x_109, 3, x_105);
lean_ctor_set(x_109, 4, x_108);
lean_ctor_set(x_109, 5, x_107);
lean_inc(x_5);
x_110 = lean_metavar_ctx_get_expr_assignment(x_103, x_5);
lean_inc(x_3);
x_111 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_109, x_106);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_inc(x_3);
x_112 = l_Lean_Elab_Term_mkFreshId(x_3, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_3);
lean_inc(x_1);
x_115 = l_Lean_Elab_Term_inferType(x_1, x_3, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_113);
x_118 = l_Lean_mkFVar(x_113);
x_119 = l_Lean_Elab_Term_assignExprMVar(x_5, x_118, x_3, x_117);
lean_dec(x_3);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_2, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_2, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_2, 2);
lean_inc(x_124);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_125 = x_2;
} else {
 lean_dec_ref(x_2);
 x_125 = lean_box(0);
}
x_126 = lean_array_get_size(x_123);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_add(x_126, x_127);
lean_dec(x_126);
x_129 = l_Lean_Closure_mkNextUserName___rarg___closed__2;
x_130 = l_Lean_Name_appendIndexAfter(x_129, x_128);
x_131 = lean_unsigned_to_nat(0u);
x_132 = 0;
lean_inc(x_113);
x_133 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_113);
lean_ctor_set(x_133, 2, x_130);
lean_ctor_set(x_133, 3, x_116);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_132);
x_134 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_1, x_123, x_131);
lean_dec(x_1);
x_135 = lean_box(0);
lean_inc(x_113);
x_136 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_124, x_113, x_135);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_array_push(x_123, x_133);
if (lean_is_scalar(x_125)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_125;
}
lean_ctor_set(x_138, 0, x_122);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_113);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
if (lean_is_scalar(x_121)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_121;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_120);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
lean_dec(x_134);
x_143 = l_Array_insertAt___rarg(x_123, x_142, x_133);
lean_dec(x_142);
if (lean_is_scalar(x_125)) {
 x_144 = lean_alloc_ctor(0, 3, 0);
} else {
 x_144 = x_125;
}
lean_ctor_set(x_144, 0, x_122);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_136);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_113);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
if (lean_is_scalar(x_121)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_121;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_120);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_113);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_115, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_115, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_150 = x_115;
} else {
 lean_dec_ref(x_115);
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
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_ctor_get(x_110, 0);
lean_inc(x_152);
lean_dec(x_110);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_2);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_111);
return x_155;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_Match_29__mkLocalDeclFor___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_name_eq(x_9, x_2);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_12 = lean_array_fget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_3, x_2, x_13);
x_25 = x_12;
x_30 = l_Lean_BinderInfo_inhabited;
x_31 = lean_box(x_30);
x_32 = lean_array_get(x_31, x_1, x_2);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_Lean_BinderInfo_isExplicit(x_33);
if (x_34 == 0)
{
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
x_38 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(x_4, x_35, x_36, x_37, x_13);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_25);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
x_15 = x_40;
x_16 = x_6;
goto block_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = l___private_Lean_Elab_Match_25__alreadyVisited(x_35, x_4, x_5, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l___private_Lean_Elab_Match_26__markAsVisited(x_35, x_46, x_5, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_48, 0, x_53);
x_15 = x_48;
x_16 = x_49;
goto block_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_15 = x_57;
x_16 = x_49;
goto block_24;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_35);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = !lean_is_exclusive(x_42);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_42, 0);
lean_dec(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_42, 0, x_61);
x_15 = x_42;
x_16 = x_58;
goto block_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_dec(x_42);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_25);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_15 = x_64;
x_16 = x_58;
goto block_24;
}
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_26 = x_65;
goto block_29;
}
}
else
{
lean_object* x_66; 
lean_inc(x_5);
x_66 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_25, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_15 = x_67;
x_16 = x_68;
goto block_24;
}
else
{
uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_24:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = x_17;
x_22 = lean_array_fset(x_14, x_2, x_21);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_22;
x_4 = x_18;
x_6 = x_16;
goto _start;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_15 = x_28;
x_16 = x_6;
goto block_24;
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
x_10 = lean_name_eq(x_9, x_2);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_12 = lean_array_fget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_3, x_2, x_13);
x_25 = x_12;
x_30 = l_Lean_BinderInfo_inhabited;
x_31 = lean_box(x_30);
x_32 = lean_array_get(x_31, x_1, x_2);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_Lean_BinderInfo_isExplicit(x_33);
if (x_34 == 0)
{
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
x_37 = lean_array_get_size(x_36);
x_38 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(x_4, x_35, x_36, x_37, x_13);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_25);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
x_15 = x_40;
x_16 = x_6;
goto block_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = l___private_Lean_Elab_Match_25__alreadyVisited(x_35, x_4, x_5, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l___private_Lean_Elab_Match_26__markAsVisited(x_35, x_46, x_5, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_48, 0, x_53);
x_15 = x_48;
x_16 = x_49;
goto block_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_15 = x_57;
x_16 = x_49;
goto block_24;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_35);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = !lean_is_exclusive(x_42);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_42, 0);
lean_dec(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_42, 0, x_61);
x_15 = x_42;
x_16 = x_58;
goto block_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_dec(x_42);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_25);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_15 = x_64;
x_16 = x_58;
goto block_24;
}
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_26 = x_65;
goto block_29;
}
}
else
{
lean_object* x_66; 
lean_inc(x_5);
x_66 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_25, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_15 = x_67;
x_16 = x_68;
goto block_24;
}
else
{
uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_24:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = x_17;
x_22 = lean_array_fset(x_14, x_2, x_21);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_22;
x_4 = x_18;
x_6 = x_16;
goto _start;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_15 = x_28;
x_16 = x_6;
goto block_24;
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
x_10 = lean_name_eq(x_9, x_2);
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
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_16 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(x_10, x_15, x_3, x_13);
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
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set(x_18, 0, x_1);
return x_16;
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
lean_ctor_set(x_1, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
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
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_14);
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_free_object(x_1);
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
uint8_t x_35; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
lean_inc(x_3);
x_41 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_39, x_2, x_3, x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(x_40, x_45, x_3, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_50);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_44);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_58 = x_46;
} else {
 lean_dec_ref(x_46);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_40);
lean_dec(x_3);
x_60 = lean_ctor_get(x_41, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_62 = x_41;
} else {
 lean_dec_ref(x_41);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_name_eq(x_9, x_2);
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
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_inaccessible_x3f(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Expr_arrayLit_x3f(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity___main(x_1, x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isNatLit(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isStringLit(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isCharLit(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isFVar(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isMVar(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Elab_Term_whnf(x_1, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_expr_eqv(x_16, x_1);
if (x_18 == 0)
{
lean_dec(x_1);
x_1 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_16);
x_20 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getEnv___rarg(x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_21);
x_26 = lean_environment_find(x_24, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_27 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_25);
lean_dec(x_2);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 6)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_30);
x_32 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
lean_inc(x_1);
x_36 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_33, x_35);
x_37 = lean_array_get_size(x_36);
x_38 = lean_ctor_get(x_29, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 4);
lean_inc(x_39);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_39);
x_41 = lean_nat_dec_eq(x_37, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_21);
x_42 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_25);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_47 = l_Array_extract___rarg(x_36, x_30, x_38);
x_48 = l_Array_extract___rarg(x_36, x_38, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_49 = l___private_Lean_Elab_Match_30__getFieldsBinderInfo(x_29);
lean_dec(x_29);
x_50 = x_48;
x_51 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4___boxed), 6, 3);
lean_closure_set(x_51, 0, x_49);
lean_closure_set(x_51, 1, x_30);
lean_closure_set(x_51, 2, x_50);
x_52 = x_51;
x_53 = lean_apply_3(x_52, x_2, x_3, x_25);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Array_toList___rarg(x_47);
lean_dec(x_47);
x_59 = l_Array_toList___rarg(x_57);
lean_dec(x_57);
x_60 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_60, 0, x_21);
lean_ctor_set(x_60, 1, x_22);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_55, 0, x_60);
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = l_Array_toList___rarg(x_47);
lean_dec(x_47);
x_64 = l_Array_toList___rarg(x_61);
lean_dec(x_61);
x_65 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_22);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_53, 0, x_66);
return x_53;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
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
x_72 = l_Array_toList___rarg(x_47);
lean_dec(x_47);
x_73 = l_Array_toList___rarg(x_69);
lean_dec(x_69);
x_74 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_22);
lean_ctor_set(x_74, 2, x_72);
lean_ctor_set(x_74, 3, x_73);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_47);
lean_dec(x_22);
lean_dec(x_21);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
return x_53;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
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
lean_object* x_81; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_21);
x_81 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_25);
lean_dec(x_2);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_20);
x_82 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_17);
lean_dec(x_2);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
return x_15;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
x_87 = l___private_Lean_Elab_Match_29__mkLocalDeclFor(x_1, x_2, x_3, x_4);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = l_Lean_Expr_fvarId_x21(x_1);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_array_get_size(x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_2, x_88, x_89, x_90, x_91);
lean_dec(x_90);
lean_dec(x_89);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_88);
x_93 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = l___private_Lean_Elab_Match_25__alreadyVisited(x_88, x_2, x_3, x_4);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_1);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
lean_inc(x_88);
x_104 = l___private_Lean_Elab_Match_26__markAsVisited(x_88, x_103, x_3, x_102);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
lean_dec(x_108);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_88);
lean_ctor_set(x_106, 0, x_109);
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_88);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_104, 0, x_112);
return x_104;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_104, 0);
x_114 = lean_ctor_get(x_104, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_104);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_88);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_114);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_88);
lean_dec(x_3);
x_120 = !lean_is_exclusive(x_98);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_98, 0);
lean_dec(x_121);
x_122 = !lean_is_exclusive(x_99);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_99, 0);
lean_dec(x_123);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_99, 0, x_124);
return x_98;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_99, 1);
lean_inc(x_125);
lean_dec(x_99);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_1);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
lean_ctor_set(x_98, 0, x_127);
return x_98;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_98, 1);
lean_inc(x_128);
lean_dec(x_98);
x_129 = lean_ctor_get(x_99, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_130 = x_99;
} else {
 lean_dec_ref(x_99);
 x_130 = lean_box(0);
}
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_1);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_3);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_1);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_2);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_4);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_3);
x_137 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_137, 0, x_1);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_2);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_4);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_3);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_1);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_2);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_4);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_unsigned_to_nat(0u);
x_144 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_143);
x_145 = lean_unsigned_to_nat(2u);
x_146 = lean_nat_sub(x_144, x_145);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_sub(x_146, x_147);
lean_dec(x_146);
x_149 = l_Lean_Expr_getRevArg_x21___main(x_1, x_148);
lean_inc(x_3);
x_150 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_149, x_2, x_3, x_4);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_150, 0);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_150, 1);
x_155 = lean_ctor_get(x_152, 0);
x_156 = lean_ctor_get(x_152, 1);
x_157 = lean_nat_sub(x_144, x_147);
lean_dec(x_144);
x_158 = lean_nat_sub(x_157, x_147);
lean_dec(x_157);
x_159 = l_Lean_Expr_getRevArg_x21___main(x_1, x_158);
lean_dec(x_1);
if (lean_obj_tag(x_159) == 1)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_3);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_152, 0, x_161);
return x_150;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec(x_159);
lean_free_object(x_152);
lean_dec(x_156);
lean_dec(x_155);
lean_free_object(x_150);
x_162 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_163 = l_Lean_Elab_Term_throwError___rarg(x_162, x_3, x_154);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
return x_163;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_163);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_150, 1);
x_169 = lean_ctor_get(x_152, 0);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_152);
x_171 = lean_nat_sub(x_144, x_147);
lean_dec(x_144);
x_172 = lean_nat_sub(x_171, x_147);
lean_dec(x_171);
x_173 = l_Lean_Expr_getRevArg_x21___main(x_1, x_172);
lean_dec(x_1);
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_3);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_169);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_170);
lean_ctor_set(x_150, 0, x_176);
return x_150;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
lean_free_object(x_150);
x_177 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_178 = l_Lean_Elab_Term_throwError___rarg(x_177, x_3, x_168);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_150, 0);
x_184 = lean_ctor_get(x_150, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_150);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_187 = x_183;
} else {
 lean_dec_ref(x_183);
 x_187 = lean_box(0);
}
x_188 = lean_nat_sub(x_144, x_147);
lean_dec(x_144);
x_189 = lean_nat_sub(x_188, x_147);
lean_dec(x_188);
x_190 = l_Lean_Expr_getRevArg_x21___main(x_1, x_189);
lean_dec(x_1);
if (lean_obj_tag(x_190) == 1)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_3);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_185);
if (lean_is_scalar(x_187)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_187;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_186);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_184);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_190);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
x_195 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_196 = l_Lean_Elab_Term_throwError___rarg(x_195, x_3, x_184);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_144);
lean_dec(x_3);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_150);
if (x_201 == 0)
{
return x_150;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_150, 0);
x_203 = lean_ctor_get(x_150, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_150);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_1);
x_205 = lean_ctor_get(x_6, 0);
lean_inc(x_205);
lean_dec(x_6);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(x_207, x_2, x_3, x_4);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_210, 0, x_213);
return x_208;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_210, 0);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_210);
x_216 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_216, 0, x_206);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
lean_ctor_set(x_208, 0, x_217);
return x_208;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_208, 0);
x_219 = lean_ctor_get(x_208, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_208);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_223, 0, x_206);
lean_ctor_set(x_223, 1, x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_219);
return x_225;
}
}
else
{
uint8_t x_226; 
lean_dec(x_206);
x_226 = !lean_is_exclusive(x_208);
if (x_226 == 0)
{
return x_208;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_208, 0);
x_228 = lean_ctor_get(x_208, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_208);
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
lean_object* x_230; lean_object* x_231; 
lean_dec(x_1);
x_230 = lean_ctor_get(x_5, 0);
lean_inc(x_230);
lean_dec(x_5);
if (lean_obj_tag(x_230) == 1)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_230, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 1);
lean_inc(x_237);
x_238 = lean_array_get_size(x_237);
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(x_2, x_236, x_237, x_238, x_239);
lean_dec(x_238);
lean_dec(x_237);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_236);
lean_dec(x_3);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_230);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_2);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_4);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = l___private_Lean_Elab_Match_25__alreadyVisited(x_236, x_2, x_3, x_4);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_unbox(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
lean_dec(x_244);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = l___private_Lean_Elab_Match_26__markAsVisited(x_236, x_249, x_3, x_248);
lean_dec(x_3);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_252, 0);
lean_dec(x_254);
x_255 = l_Lean_Expr_fvarId_x21(x_230);
lean_dec(x_230);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_252, 0, x_256);
return x_250;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_252, 1);
lean_inc(x_257);
lean_dec(x_252);
x_258 = l_Lean_Expr_fvarId_x21(x_230);
lean_dec(x_230);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
lean_ctor_set(x_250, 0, x_260);
return x_250;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_250, 0);
x_262 = lean_ctor_get(x_250, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_250);
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
x_265 = l_Lean_Expr_fvarId_x21(x_230);
lean_dec(x_230);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
if (lean_is_scalar(x_264)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_264;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_263);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_262);
return x_268;
}
}
else
{
uint8_t x_269; 
lean_dec(x_236);
lean_dec(x_3);
x_269 = !lean_is_exclusive(x_244);
if (x_269 == 0)
{
lean_object* x_270; uint8_t x_271; 
x_270 = lean_ctor_get(x_244, 0);
lean_dec(x_270);
x_271 = !lean_is_exclusive(x_245);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_245, 0);
lean_dec(x_272);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_230);
lean_ctor_set(x_245, 0, x_273);
return x_244;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_245, 1);
lean_inc(x_274);
lean_dec(x_245);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_230);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
lean_ctor_set(x_244, 0, x_276);
return x_244;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_277 = lean_ctor_get(x_244, 1);
lean_inc(x_277);
lean_dec(x_244);
x_278 = lean_ctor_get(x_245, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_279 = x_245;
} else {
 lean_dec_ref(x_245);
 x_279 = lean_box(0);
}
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_230);
if (lean_is_scalar(x_279)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_279;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_278);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_277);
return x_282;
}
}
}
}
else
{
lean_object* x_283; 
lean_dec(x_3);
x_283 = lean_box(0);
x_231 = x_283;
goto block_235;
}
block_235:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_231);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_230);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_2);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_4);
return x_234;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
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
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_2, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = x_11;
lean_inc(x_4);
x_15 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_14, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_13, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_3 = x_19;
x_5 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_13, 4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_13, 4, x_17);
x_18 = l_Lean_Meta_instantiateLocalDeclMVars(x_12, x_16, x_13);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_19;
x_25 = lean_array_fset(x_11, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 2);
x_30 = lean_ctor_get(x_13, 3);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_instantiateLocalDeclMVars(x_12, x_33, x_35);
lean_dec(x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_38, x_31);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_1, x_40);
x_42 = x_37;
x_43 = lean_array_fset(x_11, x_1, x_42);
lean_dec(x_1);
x_1 = x_41;
x_2 = x_43;
x_4 = x_39;
goto _start;
}
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
lean_object* l_Lean_Elab_Term_withDepElimPatterns___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = x_2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__1), 5, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = l_Lean_NameSet_empty;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_9);
x_11 = x_8;
lean_inc(x_4);
x_12 = lean_apply_3(x_11, x_10, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = x_17;
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__2), 4, 2);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_18);
x_20 = x_19;
lean_inc(x_4);
x_21 = lean_apply_2(x_20, x_4, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_getLCtx(x_4, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__3(x_22, x_22, x_7, x_25);
x_28 = l_Array_iterateMAux___main___at_Lean_Elab_Term_withDepElimPatterns___spec__4(x_22, x_22, x_7, x_27);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_dec(x_32);
lean_ctor_set(x_30, 1, x_28);
x_33 = lean_apply_4(x_3, x_22, x_15, x_4, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 2);
x_36 = lean_ctor_get(x_30, 3);
x_37 = lean_ctor_get(x_30, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_4, 0, x_38);
x_39 = lean_apply_4(x_3, x_22, x_15, x_4, x_26);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
x_42 = lean_ctor_get(x_4, 2);
x_43 = lean_ctor_get(x_4, 3);
x_44 = lean_ctor_get(x_4, 4);
x_45 = lean_ctor_get(x_4, 5);
x_46 = lean_ctor_get(x_4, 6);
x_47 = lean_ctor_get(x_4, 7);
x_48 = lean_ctor_get(x_4, 8);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_52 = lean_ctor_get(x_4, 9);
lean_inc(x_52);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_40, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 x_57 = x_40;
} else {
 lean_dec_ref(x_40);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_28);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
x_59 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
lean_ctor_set(x_59, 5, x_45);
lean_ctor_set(x_59, 6, x_46);
lean_ctor_set(x_59, 7, x_47);
lean_ctor_set(x_59, 8, x_48);
lean_ctor_set(x_59, 9, x_52);
lean_ctor_set_uint8(x_59, sizeof(void*)*10, x_49);
lean_ctor_set_uint8(x_59, sizeof(void*)*10 + 1, x_50);
lean_ctor_set_uint8(x_59, sizeof(void*)*10 + 2, x_51);
x_60 = lean_apply_4(x_3, x_22, x_15, x_59, x_26);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_21);
if (x_61 == 0)
{
return x_21;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_21, 0);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_21);
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
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_12);
if (x_65 == 0)
{
return x_12;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_12, 0);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_12);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
lean_object* l_Lean_Elab_Term_withDepElimPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDepElimPatterns___rarg), 5, 0);
return x_2;
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_instantiateMVars(x_12, x_3, x_4);
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
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Array_toList___rarg(x_3);
x_8 = l_Array_toList___rarg(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_1, x_9, x_2, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_empty___closed__1;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_24__elabPatternsAux___boxed), 6, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_8);
lean_inc(x_5);
x_10 = l_Lean_Elab_Term_withSynthesize___rarg(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_finalizePatternDecls(x_1, x_5, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = x_13;
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__withElaboratedLHS___spec__1), 4, 2);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_18);
x_20 = x_19;
lean_inc(x_5);
x_21 = lean_apply_2(x_20, x_5, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1___boxed), 6, 2);
lean_closure_set(x_24, 0, x_4);
lean_closure_set(x_24, 1, x_14);
x_25 = l_Lean_Elab_Term_withDepElimPatterns___rarg(x_16, x_22, x_24, x_5, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
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
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
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
x_8 = l_Lean_Name_toString___closed__1;
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
x_14 = l_Lean_Name_toString___closed__1;
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
x_27 = l_Lean_Name_toString___closed__1;
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
x_31 = l_Lean_Name_toString___closed__1;
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
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
lean_inc(x_5);
x_9 = l_Lean_Elab_Term_elabTermEnsuringType(x_7, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_List_redLength___main___rarg(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = l_List_toArrayAux___main___rarg(x_12, x_14);
x_16 = x_15;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_Match_2__withAltsAux___main___spec__1(x_17, x_16);
x_19 = x_18;
x_20 = l_Array_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_mkLambda(x_19, x_10, x_5, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_getOptions(x_5, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_2);
x_28 = l_Lean_checkTraceOption(x_26, x_2);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_free_object(x_24);
lean_inc(x_22);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_31 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_logTrace(x_2, x_32, x_5, x_27);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_22);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
lean_inc(x_2);
x_42 = l_Lean_checkTraceOption(x_40, x_2);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_22);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_22);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_22);
x_46 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_Term_logTrace(x_2, x_47, x_5, x_41);
lean_dec(x_5);
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
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_22);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_19);
x_57 = l_Lean_mkThunk(x_10);
x_58 = l_Lean_Elab_Term_getOptions(x_5, x_11);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_2);
x_62 = l_Lean_checkTraceOption(x_60, x_2);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_58, 0, x_63);
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_free_object(x_58);
lean_inc(x_57);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_57);
x_65 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_Term_logTrace(x_2, x_66, x_5, x_61);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_57);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set(x_72, 1, x_57);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_58, 0);
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_58);
lean_inc(x_2);
x_76 = l_Lean_checkTraceOption(x_74, x_2);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_5);
lean_dec(x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_3);
lean_ctor_set(x_77, 1, x_57);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_57);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_57);
x_80 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_Term_logTrace(x_2, x_81, x_5, x_75);
lean_dec(x_5);
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
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_3);
lean_ctor_set(x_85, 1, x_57);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_9);
if (x_87 == 0)
{
return x_9;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__1), 6, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l___private_Lean_Elab_Match_31__withElaboratedLHS___rarg(x_4, x_7, x_3, x_8, x_5, x_6);
return x_9;
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
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 9);
x_8 = l_Lean_Elab_replaceRef(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_ctor_set(x_3, 9, x_8);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Match_21__collectPatternVars(x_1, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Elab_Term_getOptions(x_3, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_18 = l_Lean_checkTraceOption(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 6, 3);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_2);
x_20 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_12, x_19, x_3, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = l_Array_toList___rarg(x_12);
x_22 = l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_21);
x_23 = l_Array_HasRepr___rarg___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Elab_Term_elabMatchAltView___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_Term_logTrace(x_17, x_28, x_3, x_16);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 6, 3);
lean_closure_set(x_31, 0, x_13);
lean_closure_set(x_31, 1, x_17);
lean_closure_set(x_31, 2, x_2);
x_32 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_12, x_31, x_3, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get(x_3, 3);
x_41 = lean_ctor_get(x_3, 4);
x_42 = lean_ctor_get(x_3, 5);
x_43 = lean_ctor_get(x_3, 6);
x_44 = lean_ctor_get(x_3, 7);
x_45 = lean_ctor_get(x_3, 8);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_49 = lean_ctor_get(x_3, 9);
lean_inc(x_49);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_50 = l_Lean_Elab_replaceRef(x_5, x_49);
lean_dec(x_49);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_38);
lean_ctor_set(x_51, 2, x_39);
lean_ctor_set(x_51, 3, x_40);
lean_ctor_set(x_51, 4, x_41);
lean_ctor_set(x_51, 5, x_42);
lean_ctor_set(x_51, 6, x_43);
lean_ctor_set(x_51, 7, x_44);
lean_ctor_set(x_51, 8, x_45);
lean_ctor_set(x_51, 9, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*10, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*10 + 1, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*10 + 2, x_48);
lean_inc(x_51);
x_52 = l___private_Lean_Elab_Match_21__collectPatternVars(x_1, x_51, x_4);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Elab_Term_getOptions(x_51, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_61 = l_Lean_checkTraceOption(x_58, x_60);
lean_dec(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 6, 3);
lean_closure_set(x_62, 0, x_56);
lean_closure_set(x_62, 1, x_60);
lean_closure_set(x_62, 2, x_2);
x_63 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_55, x_62, x_51, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = l_Array_toList___rarg(x_55);
x_65 = l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_64);
x_66 = l_Array_HasRepr___rarg___closed__1;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_Elab_Term_elabMatchAltView___closed__3;
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_Term_logTrace(x_60, x_71, x_51, x_59);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed), 6, 3);
lean_closure_set(x_74, 0, x_56);
lean_closure_set(x_74, 1, x_60);
lean_closure_set(x_74, 2, x_2);
x_75 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_55, x_74, x_51, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_51);
lean_dec(x_2);
x_76 = lean_ctor_get(x_52, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_52, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_78 = x_52;
} else {
 lean_dec_ref(x_52);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
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
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabMatchAltView___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_getLevel(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_mkSort(x_6);
x_9 = l_Lean_Meta_mkForall(x_1, x_8, x_3, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_mkMotiveType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkMotiveType___lambda__1), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_mkMotiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Elab_Term_mkMotiveType___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_10, x_8, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_13, x_7);
lean_ctor_set(x_11, 1, x_14);
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
x_17 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_16, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_20);
x_23 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_21, x_7);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_3);
x_26 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_24);
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_25, x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Elab_Term_mkMotiveType___closed__1;
x_39 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_38, x_35, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_41, x_33);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
lean_inc(x_3);
x_48 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_45);
x_49 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_46, x_33);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkMotiveType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkMotiveType(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_Match_mkElim(x_1, x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
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
x_17 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Lean_Elab_Term_2__fromMetaException(x_4, x_20);
x_23 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Lean_Elab_Term_2__fromMetaException(x_4, x_24);
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_Match_mkElim(x_1, x_2, x_3, x_35, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_42 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_40, x_33);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
lean_inc(x_4);
x_47 = l___private_Lean_Elab_Term_2__fromMetaException(x_4, x_44);
x_48 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_45, x_33);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
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
lean_object* l_Lean_Elab_Term_reportElimResultErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_List_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_6 = l_Lean_Meta_Match_counterExamplesToMessageData(x_4);
x_7 = l_Lean_Elab_Term_reportElimResultErrors___closed__4;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_Term_throwError___rarg(x_8, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_List_isEmpty___rarg(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_List_map___main___at_Lean_Elab_Term_reportElimResultErrors___spec__1(x_14);
x_17 = l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_Term_reportElimResultErrors___closed__7;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_throwError___rarg(x_21, x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_14 = l_Lean_Elab_Term_elabMatchAltView(x_13, x_1, x_4, x_5);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambda), 4, 0);
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
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_get_size(x_1);
lean_inc(x_5);
x_8 = l___private_Lean_Elab_Match_5__elabMatchOptType(x_3, x_7, x_5, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_expandMacrosInPatterns(x_2, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_14 = l___private_Lean_Elab_Match_7__elabDiscrs(x_1, x_9, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_174 = l_Lean_Elab_Term_getOptions(x_5, x_16);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_178 = l_Lean_checkTraceOption(x_175, x_177);
lean_dec(x_175);
if (x_178 == 0)
{
x_17 = x_176;
goto block_173;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc(x_9);
x_179 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_179, 0, x_9);
x_180 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__9;
x_181 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = l_Lean_Elab_Term_logTrace(x_177, x_181, x_5, x_176);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_17 = x_183;
goto block_173;
}
block_173:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = x_12;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_20 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__1), 5, 3);
lean_closure_set(x_20, 0, x_9);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_18);
x_21 = x_20;
lean_inc(x_5);
x_22 = lean_apply_2(x_21, x_5, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = x_23;
lean_inc(x_25);
x_26 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__2(x_19, x_25);
x_27 = x_26;
x_28 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_32__elabMatchAux___spec__3(x_19, x_25);
x_29 = x_28;
lean_inc(x_5);
lean_inc(x_9);
x_30 = l_Lean_Elab_Term_mkMotiveType(x_9, x_4, x_5, x_24);
lean_dec(x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_32, 4);
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
x_37 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_32, 4, x_37);
x_38 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__1;
x_39 = l_Lean_Meta_forallTelescopeReducing___rarg(x_9, x_38, x_36, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_5);
x_42 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_31, x_41, x_35);
x_43 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__3;
lean_inc(x_5);
x_44 = l_Lean_Elab_Term_mkAuxName(x_43, x_5, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Array_toList___rarg(x_29);
lean_dec(x_29);
lean_inc(x_5);
x_48 = l_Lean_Elab_Term_mkElim(x_45, x_33, x_47, x_5, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_5);
lean_inc(x_49);
x_51 = l_Lean_Elab_Term_reportElimResultErrors(x_49, x_5, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = l_Lean_mkApp(x_53, x_40);
x_55 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_15, x_15, x_19, x_54);
lean_dec(x_15);
x_56 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_19, x_55);
lean_dec(x_27);
x_57 = l_Lean_Elab_Term_getOptions(x_5, x_52);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_62 = l_Lean_checkTraceOption(x_59, x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_dec(x_5);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_57);
lean_inc(x_56);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_56);
x_64 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Elab_Term_logTrace(x_61, x_65, x_5, x_60);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_56);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_74 = l_Lean_checkTraceOption(x_71, x_73);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_5);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_56);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_56);
x_77 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_Elab_Term_logTrace(x_73, x_78, x_5, x_72);
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
lean_ctor_set(x_82, 0, x_56);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_49);
lean_dec(x_40);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_51);
if (x_83 == 0)
{
return x_51;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_51, 0);
x_85 = lean_ctor_get(x_51, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_51);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_40);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_48);
if (x_87 == 0)
{
return x_48;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_48, 0);
x_89 = lean_ctor_get(x_48, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_48);
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
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
x_91 = !lean_is_exclusive(x_44);
if (x_91 == 0)
{
return x_44;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_44, 0);
x_93 = lean_ctor_get(x_44, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_44);
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
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_15);
x_95 = !lean_is_exclusive(x_39);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_39, 0);
x_97 = lean_ctor_get(x_39, 1);
lean_inc(x_5);
x_98 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_96);
x_99 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_31, x_97, x_35);
lean_ctor_set(x_39, 1, x_99);
lean_ctor_set(x_39, 0, x_98);
return x_39;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_39, 0);
x_101 = lean_ctor_get(x_39, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_39);
lean_inc(x_5);
x_102 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_100);
x_103 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_31, x_101, x_35);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_32, 0);
x_106 = lean_ctor_get(x_32, 1);
x_107 = lean_ctor_get(x_32, 2);
x_108 = lean_ctor_get(x_32, 3);
x_109 = lean_ctor_get(x_32, 4);
x_110 = lean_ctor_get(x_32, 5);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_32);
x_111 = lean_ctor_get(x_5, 0);
lean_inc(x_111);
x_112 = l_Lean_TraceState_Inhabited___closed__1;
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_106);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_108);
lean_ctor_set(x_113, 4, x_112);
lean_ctor_set(x_113, 5, x_110);
x_114 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__1;
x_115 = l_Lean_Meta_forallTelescopeReducing___rarg(x_9, x_114, x_111, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_5);
x_118 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_31, x_117, x_109);
x_119 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__3;
lean_inc(x_5);
x_120 = l_Lean_Elab_Term_mkAuxName(x_119, x_5, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Array_toList___rarg(x_29);
lean_dec(x_29);
lean_inc(x_5);
x_124 = l_Lean_Elab_Term_mkElim(x_121, x_33, x_123, x_5, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_5);
lean_inc(x_125);
x_127 = l_Lean_Elab_Term_reportElimResultErrors(x_125, x_5, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
lean_dec(x_125);
x_130 = l_Lean_mkApp(x_129, x_116);
x_131 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_15, x_15, x_19, x_130);
lean_dec(x_15);
x_132 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_19, x_131);
lean_dec(x_27);
x_133 = l_Lean_Elab_Term_getOptions(x_5, x_128);
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
x_137 = l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__13;
x_138 = l_Lean_checkTraceOption(x_134, x_137);
lean_dec(x_134);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_5);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_135);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_136);
lean_inc(x_132);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_132);
x_141 = l___private_Lean_Elab_Match_32__elabMatchAux___closed__6;
x_142 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_Elab_Term_logTrace(x_137, x_142, x_5, x_135);
lean_dec(x_5);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_132);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_125);
lean_dec(x_116);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
x_147 = lean_ctor_get(x_127, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_127, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_149 = x_127;
} else {
 lean_dec_ref(x_127);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_116);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
x_151 = lean_ctor_get(x_124, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_124, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_153 = x_124;
} else {
 lean_dec_ref(x_124);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_116);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
x_155 = lean_ctor_get(x_120, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_120, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_157 = x_120;
} else {
 lean_dec_ref(x_120);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_15);
x_159 = lean_ctor_get(x_115, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_115, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_161 = x_115;
} else {
 lean_dec_ref(x_115);
 x_161 = lean_box(0);
}
lean_inc(x_5);
x_162 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_159);
x_163 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_31, x_160, x_109);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_5);
x_165 = !lean_is_exclusive(x_30);
if (x_165 == 0)
{
return x_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_30, 0);
x_167 = lean_ctor_get(x_30, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_30);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_22);
if (x_169 == 0)
{
return x_22;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_22, 0);
x_171 = lean_ctor_get(x_22, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_22);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_184 = !lean_is_exclusive(x_14);
if (x_184 == 0)
{
return x_14;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_14, 0);
x_186 = lean_ctor_get(x_14, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_14);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_188 = !lean_is_exclusive(x_11);
if (x_188 == 0)
{
return x_11;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_11, 0);
x_190 = lean_ctor_get(x_11, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_11);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_8);
if (x_192 == 0)
{
return x_8;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_8, 0);
x_194 = lean_ctor_get(x_8, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_8);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_32__elabMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_32__elabMatchAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_33__waitExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Term_mkFreshTypeMVar(x_6, x_7, x_2, x_5);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
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
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Match_33__waitExpectedType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_empty___closed__1;
x_14 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_11, x_10, x_12, x_13);
lean_dec(x_10);
x_15 = x_14;
x_16 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_34__elabMatchCore___spec__1(x_12, x_15);
x_17 = x_16;
x_18 = l___private_Lean_Elab_Match_8__getMatchAlts(x_1);
x_19 = l_Lean_Syntax_getArg(x_1, x_11);
x_20 = l___private_Lean_Elab_Match_32__elabMatchAux(x_17, x_18, x_19, x_6, x_3, x_7);
lean_dec(x_19);
lean_dec(x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Match_34__elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_34__elabMatchCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_openRenamingItem___elambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_setOptionFromString___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
x_2 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
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
x_9 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
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
x_15 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
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
x_31 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
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
x_37 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_38 = lean_array_push(x_37, x_36);
x_39 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
x_40 = lean_array_push(x_38, x_39);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_42 = lean_array_push(x_40, x_41);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_44 = lean_array_push(x_42, x_43);
x_45 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_33, x_46);
x_48 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
x_49 = lean_array_push(x_47, x_48);
x_50 = lean_array_push(x_33, x_26);
x_51 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6;
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_push(x_52, x_32);
x_54 = l_Lean_Parser_Term_eq___elambda__1___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_33, x_55);
x_57 = lean_array_push(x_56, x_48);
x_58 = lean_array_push(x_57, x_22);
x_59 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_49, x_60);
x_62 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
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
x_64 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7;
x_65 = lean_array_push(x_64, x_22);
x_66 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
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
x_78 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
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
x_84 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_85 = lean_array_push(x_84, x_83);
x_86 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
x_87 = lean_array_push(x_85, x_86);
x_88 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_89 = lean_array_push(x_87, x_88);
x_90 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_91 = lean_array_push(x_89, x_90);
x_92 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_80, x_93);
x_95 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
x_96 = lean_array_push(x_94, x_95);
x_97 = lean_array_push(x_80, x_73);
x_98 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_array_push(x_99, x_79);
x_101 = l_Lean_Parser_Term_eq___elambda__1___closed__2;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_80, x_102);
x_104 = lean_array_push(x_103, x_95);
x_105 = lean_array_push(x_104, x_68);
x_106 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_96, x_107);
x_109 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
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
x_112 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7;
x_113 = lean_array_push(x_112, x_68);
x_114 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
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
x_122 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
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
x_139 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__2;
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
x_145 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_146 = lean_array_push(x_145, x_144);
x_147 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__4;
x_148 = lean_array_push(x_146, x_147);
x_149 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_150 = lean_array_push(x_148, x_149);
x_151 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_152 = lean_array_push(x_150, x_151);
x_153 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_array_push(x_141, x_154);
x_156 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__5;
x_157 = lean_array_push(x_155, x_156);
x_158 = lean_array_push(x_141, x_134);
x_159 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6;
x_160 = lean_array_push(x_158, x_159);
x_161 = lean_array_push(x_160, x_140);
x_162 = l_Lean_Parser_Term_eq___elambda__1___closed__2;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_array_push(x_141, x_163);
x_165 = lean_array_push(x_164, x_156);
x_166 = lean_array_push(x_165, x_128);
x_167 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_push(x_157, x_168);
x_170 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
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
x_173 = l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7;
x_174 = lean_array_push(x_173, x_128);
x_175 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
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
x_7 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
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
x_2 = l_Lean_Meta_mkEqRefl___closed__2;
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
lean_object* _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__9;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
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
x_10 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
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
x_27 = l_Lean_Meta_mkEqRefl___closed__2;
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
x_35 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Lean_mkAppStx___closed__8;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__6;
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
x_20 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_32 = lean_unsigned_to_nat(5u);
x_33 = l_Lean_Syntax_getArg(x_31, x_32);
x_34 = l_Lean_Syntax_getArgs(x_33);
lean_dec(x_33);
x_35 = l___private_Lean_Elab_Match_40__mkNewAlts(x_6, x_34, x_2, x_28);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Syntax_setArg(x_31, x_32, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_35, 0, x_40);
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Syntax_setArg(x_31, x_32, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_31);
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
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
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_34; lean_object* x_1334; uint8_t x_1335; 
x_1334 = l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_inc(x_1);
x_1335 = l_Lean_Syntax_isOfKind(x_1, x_1334);
if (x_1335 == 0)
{
uint8_t x_1336; 
x_1336 = 0;
x_34 = x_1336;
goto block_1333;
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; uint8_t x_1340; 
x_1337 = l_Lean_Syntax_getArgs(x_1);
x_1338 = lean_array_get_size(x_1337);
lean_dec(x_1337);
x_1339 = lean_unsigned_to_nat(6u);
x_1340 = lean_nat_dec_eq(x_1338, x_1339);
lean_dec(x_1338);
x_34 = x_1340;
goto block_1333;
}
block_33:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_34__elabMatchCore(x_1, x_2, x_3, x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 7);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_3, 7, x_12);
x_13 = 1;
x_14 = l_Lean_Elab_Term_elabTerm(x_8, x_2, x_13, x_3, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
x_20 = lean_ctor_get(x_3, 5);
x_21 = lean_ctor_get(x_3, 6);
x_22 = lean_ctor_get(x_3, 7);
x_23 = lean_ctor_get(x_3, 8);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_27 = lean_ctor_get(x_3, 9);
lean_inc(x_27);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_8);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
x_30 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_19);
lean_ctor_set(x_30, 5, x_20);
lean_ctor_set(x_30, 6, x_21);
lean_ctor_set(x_30, 7, x_29);
lean_ctor_set(x_30, 8, x_23);
lean_ctor_set(x_30, 9, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 1, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 2, x_26);
x_31 = 1;
x_32 = l_Lean_Elab_Term_elabTerm(x_8, x_2, x_31, x_30, x_6);
return x_32;
}
}
}
block_1333:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_35 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_getEnv___rarg(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 4);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_environment_main_module(x_40);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_inc(x_1);
x_52 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_51, x_46);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_39, 5);
lean_dec(x_54);
x_55 = lean_ctor_get(x_39, 4);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_39, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_39, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_39, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
lean_ctor_set(x_39, 5, x_61);
x_5 = x_60;
x_6 = x_39;
goto block_33;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_41);
lean_ctor_set(x_64, 1, x_42);
lean_ctor_set(x_64, 2, x_43);
lean_ctor_set(x_64, 3, x_44);
lean_ctor_set(x_64, 4, x_45);
lean_ctor_set(x_64, 5, x_63);
x_5 = x_62;
x_6 = x_64;
goto block_33;
}
}
else
{
lean_object* x_65; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
lean_dec(x_52);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_Elab_Term_throwErrorAt___rarg(x_66, x_69, x_3, x_39);
lean_dec(x_66);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_3);
x_75 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_39);
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
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_1327; uint8_t x_1328; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = l_Lean_Syntax_getArg(x_1, x_80);
x_1327 = l_Lean_nullKind___closed__2;
lean_inc(x_81);
x_1328 = l_Lean_Syntax_isOfKind(x_81, x_1327);
if (x_1328 == 0)
{
uint8_t x_1329; 
x_1329 = 0;
x_82 = x_1329;
goto block_1326;
}
else
{
lean_object* x_1330; lean_object* x_1331; uint8_t x_1332; 
x_1330 = l_Lean_Syntax_getArgs(x_81);
x_1331 = lean_array_get_size(x_1330);
lean_dec(x_1330);
x_1332 = lean_nat_dec_eq(x_1331, x_80);
lean_dec(x_1331);
x_82 = x_1332;
goto block_1326;
}
block_1326:
{
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_81);
x_83 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Elab_Term_getEnv___rarg(x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_3, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 4);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_environment_main_module(x_88);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_84);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_inc(x_1);
x_100 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_99, x_94);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_87);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_87, 5);
lean_dec(x_102);
x_103 = lean_ctor_get(x_87, 4);
lean_dec(x_103);
x_104 = lean_ctor_get(x_87, 3);
lean_dec(x_104);
x_105 = lean_ctor_get(x_87, 2);
lean_dec(x_105);
x_106 = lean_ctor_get(x_87, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_87, 0);
lean_dec(x_107);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
lean_ctor_set(x_87, 5, x_109);
x_5 = x_108;
x_6 = x_87;
goto block_33;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_87);
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_89);
lean_ctor_set(x_112, 1, x_90);
lean_ctor_set(x_112, 2, x_91);
lean_ctor_set(x_112, 3, x_92);
lean_ctor_set(x_112, 4, x_93);
lean_ctor_set(x_112, 5, x_111);
x_5 = x_110;
x_6 = x_112;
goto block_33;
}
}
else
{
lean_object* x_113; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_100, 0);
lean_inc(x_113);
lean_dec(x_100);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_Elab_Term_throwErrorAt___rarg(x_114, x_117, x_3, x_87);
lean_dec(x_114);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_3);
x_123 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_87);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
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
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_1319; uint8_t x_1320; 
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Lean_Syntax_getArg(x_81, x_128);
lean_dec(x_81);
x_1319 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_inc(x_129);
x_1320 = l_Lean_Syntax_isOfKind(x_129, x_1319);
if (x_1320 == 0)
{
uint8_t x_1321; 
x_1321 = 0;
x_130 = x_1321;
goto block_1318;
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint8_t x_1325; 
x_1322 = l_Lean_Syntax_getArgs(x_129);
x_1323 = lean_array_get_size(x_1322);
lean_dec(x_1322);
x_1324 = lean_unsigned_to_nat(2u);
x_1325 = lean_nat_dec_eq(x_1323, x_1324);
lean_dec(x_1323);
x_130 = x_1325;
goto block_1318;
}
block_1318:
{
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_129);
x_131 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Elab_Term_getEnv___rarg(x_133);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_3, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 4);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_environment_main_module(x_136);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_132);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_inc(x_1);
x_148 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_147, x_142);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_135);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_135, 5);
lean_dec(x_150);
x_151 = lean_ctor_get(x_135, 4);
lean_dec(x_151);
x_152 = lean_ctor_get(x_135, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_135, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_135, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_135, 0);
lean_dec(x_155);
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
lean_dec(x_148);
lean_ctor_set(x_135, 5, x_157);
x_5 = x_156;
x_6 = x_135;
goto block_33;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_135);
x_158 = lean_ctor_get(x_148, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_148, 1);
lean_inc(x_159);
lean_dec(x_148);
x_160 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_160, 0, x_137);
lean_ctor_set(x_160, 1, x_138);
lean_ctor_set(x_160, 2, x_139);
lean_ctor_set(x_160, 3, x_140);
lean_ctor_set(x_160, 4, x_141);
lean_ctor_set(x_160, 5, x_159);
x_5 = x_158;
x_6 = x_160;
goto block_33;
}
}
else
{
lean_object* x_161; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_148, 0);
lean_inc(x_161);
lean_dec(x_148);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_Elab_Term_throwErrorAt___rarg(x_162, x_165, x_3, x_135);
lean_dec(x_162);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
return x_166;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_166);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; uint8_t x_172; 
lean_dec(x_3);
x_171 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_135);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
return x_171;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_171);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
lean_object* x_176; uint8_t x_177; lean_object* x_1312; uint8_t x_1313; 
x_176 = l_Lean_Syntax_getArg(x_129, x_128);
x_1312 = l_Lean_nullKind___closed__2;
lean_inc(x_176);
x_1313 = l_Lean_Syntax_isOfKind(x_176, x_1312);
if (x_1313 == 0)
{
uint8_t x_1314; 
lean_dec(x_176);
x_1314 = 0;
x_177 = x_1314;
goto block_1311;
}
else
{
lean_object* x_1315; lean_object* x_1316; uint8_t x_1317; 
x_1315 = l_Lean_Syntax_getArgs(x_176);
lean_dec(x_176);
x_1316 = lean_array_get_size(x_1315);
lean_dec(x_1315);
x_1317 = lean_nat_dec_eq(x_1316, x_128);
lean_dec(x_1316);
x_177 = x_1317;
goto block_1311;
}
block_1311:
{
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_129);
x_178 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Lean_Elab_Term_getEnv___rarg(x_180);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_182, 5);
lean_inc(x_189);
x_190 = lean_ctor_get(x_3, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 4);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_environment_main_module(x_183);
x_194 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_179);
lean_ctor_set(x_194, 2, x_191);
lean_ctor_set(x_194, 3, x_192);
lean_inc(x_1);
x_195 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_194, x_189);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_182);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_197 = lean_ctor_get(x_182, 5);
lean_dec(x_197);
x_198 = lean_ctor_get(x_182, 4);
lean_dec(x_198);
x_199 = lean_ctor_get(x_182, 3);
lean_dec(x_199);
x_200 = lean_ctor_get(x_182, 2);
lean_dec(x_200);
x_201 = lean_ctor_get(x_182, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_182, 0);
lean_dec(x_202);
x_203 = lean_ctor_get(x_195, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_195, 1);
lean_inc(x_204);
lean_dec(x_195);
lean_ctor_set(x_182, 5, x_204);
x_5 = x_203;
x_6 = x_182;
goto block_33;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_182);
x_205 = lean_ctor_get(x_195, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_195, 1);
lean_inc(x_206);
lean_dec(x_195);
x_207 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_207, 0, x_184);
lean_ctor_set(x_207, 1, x_185);
lean_ctor_set(x_207, 2, x_186);
lean_ctor_set(x_207, 3, x_187);
lean_ctor_set(x_207, 4, x_188);
lean_ctor_set(x_207, 5, x_206);
x_5 = x_205;
x_6 = x_207;
goto block_33;
}
}
else
{
lean_object* x_208; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_ctor_get(x_195, 0);
lean_inc(x_208);
lean_dec(x_195);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_Lean_Elab_Term_throwErrorAt___rarg(x_209, x_212, x_3, x_182);
lean_dec(x_209);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
return x_213;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_213);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
else
{
lean_object* x_218; uint8_t x_219; 
lean_dec(x_3);
x_218 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_182);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
return x_218;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_218, 0);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_218);
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
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_815; uint8_t x_816; uint8_t x_817; 
x_223 = l_Lean_Syntax_getArg(x_129, x_80);
lean_dec(x_129);
x_224 = lean_unsigned_to_nat(2u);
x_225 = l_Lean_Syntax_getArg(x_1, x_224);
x_815 = l_Lean_nullKind___closed__2;
lean_inc(x_225);
x_816 = l_Lean_Syntax_isOfKind(x_225, x_815);
if (x_816 == 0)
{
uint8_t x_1307; 
x_1307 = 0;
x_817 = x_1307;
goto block_1306;
}
else
{
lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; 
x_1308 = l_Lean_Syntax_getArgs(x_225);
x_1309 = lean_array_get_size(x_1308);
lean_dec(x_1308);
x_1310 = lean_nat_dec_eq(x_1309, x_128);
lean_dec(x_1309);
x_817 = x_1310;
goto block_1306;
}
block_814:
{
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_225);
lean_dec(x_223);
x_227 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Elab_Term_getEnv___rarg(x_229);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_231, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_231, 5);
lean_inc(x_238);
x_239 = lean_ctor_get(x_3, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 4);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_environment_main_module(x_232);
x_243 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_228);
lean_ctor_set(x_243, 2, x_240);
lean_ctor_set(x_243, 3, x_241);
lean_inc(x_1);
x_244 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_243, x_238);
if (lean_obj_tag(x_244) == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_231);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_246 = lean_ctor_get(x_231, 5);
lean_dec(x_246);
x_247 = lean_ctor_get(x_231, 4);
lean_dec(x_247);
x_248 = lean_ctor_get(x_231, 3);
lean_dec(x_248);
x_249 = lean_ctor_get(x_231, 2);
lean_dec(x_249);
x_250 = lean_ctor_get(x_231, 1);
lean_dec(x_250);
x_251 = lean_ctor_get(x_231, 0);
lean_dec(x_251);
x_252 = lean_ctor_get(x_244, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_244, 1);
lean_inc(x_253);
lean_dec(x_244);
lean_ctor_set(x_231, 5, x_253);
x_5 = x_252;
x_6 = x_231;
goto block_33;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_231);
x_254 = lean_ctor_get(x_244, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_244, 1);
lean_inc(x_255);
lean_dec(x_244);
x_256 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_256, 0, x_233);
lean_ctor_set(x_256, 1, x_234);
lean_ctor_set(x_256, 2, x_235);
lean_ctor_set(x_256, 3, x_236);
lean_ctor_set(x_256, 4, x_237);
lean_ctor_set(x_256, 5, x_255);
x_5 = x_254;
x_6 = x_256;
goto block_33;
}
}
else
{
lean_object* x_257; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_ctor_get(x_244, 0);
lean_inc(x_257);
lean_dec(x_244);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = l_Lean_Elab_Term_throwErrorAt___rarg(x_258, x_261, x_3, x_231);
lean_dec(x_258);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
return x_262;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_262);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
else
{
lean_object* x_267; uint8_t x_268; 
lean_dec(x_3);
x_267 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_231);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
return x_267;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_267);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
else
{
lean_object* x_272; uint8_t x_273; lean_object* x_808; uint8_t x_809; 
x_272 = l_Lean_Syntax_getArg(x_225, x_128);
lean_dec(x_225);
x_808 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_272);
x_809 = l_Lean_Syntax_isOfKind(x_272, x_808);
if (x_809 == 0)
{
uint8_t x_810; 
x_810 = 0;
x_273 = x_810;
goto block_807;
}
else
{
lean_object* x_811; lean_object* x_812; uint8_t x_813; 
x_811 = l_Lean_Syntax_getArgs(x_272);
x_812 = lean_array_get_size(x_811);
lean_dec(x_811);
x_813 = lean_nat_dec_eq(x_812, x_224);
lean_dec(x_812);
x_273 = x_813;
goto block_807;
}
block_807:
{
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_272);
lean_dec(x_223);
x_274 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Lean_Elab_Term_getEnv___rarg(x_276);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_278, 2);
lean_inc(x_282);
x_283 = lean_ctor_get(x_278, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_278, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_278, 5);
lean_inc(x_285);
x_286 = lean_ctor_get(x_3, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_286, 3);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 4);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_environment_main_module(x_279);
x_290 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_275);
lean_ctor_set(x_290, 2, x_287);
lean_ctor_set(x_290, 3, x_288);
lean_inc(x_1);
x_291 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_290, x_285);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_278);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_293 = lean_ctor_get(x_278, 5);
lean_dec(x_293);
x_294 = lean_ctor_get(x_278, 4);
lean_dec(x_294);
x_295 = lean_ctor_get(x_278, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_278, 2);
lean_dec(x_296);
x_297 = lean_ctor_get(x_278, 1);
lean_dec(x_297);
x_298 = lean_ctor_get(x_278, 0);
lean_dec(x_298);
x_299 = lean_ctor_get(x_291, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_291, 1);
lean_inc(x_300);
lean_dec(x_291);
lean_ctor_set(x_278, 5, x_300);
x_5 = x_299;
x_6 = x_278;
goto block_33;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_278);
x_301 = lean_ctor_get(x_291, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_291, 1);
lean_inc(x_302);
lean_dec(x_291);
x_303 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_303, 0, x_280);
lean_ctor_set(x_303, 1, x_281);
lean_ctor_set(x_303, 2, x_282);
lean_ctor_set(x_303, 3, x_283);
lean_ctor_set(x_303, 4, x_284);
lean_ctor_set(x_303, 5, x_302);
x_5 = x_301;
x_6 = x_303;
goto block_33;
}
}
else
{
lean_object* x_304; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_2);
lean_dec(x_1);
x_304 = lean_ctor_get(x_291, 0);
lean_inc(x_304);
lean_dec(x_291);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_308, 0, x_307);
x_309 = l_Lean_Elab_Term_throwErrorAt___rarg(x_305, x_308, x_3, x_278);
lean_dec(x_305);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
return x_309;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_309);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_3);
x_314 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_278);
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
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_583; uint8_t x_584; uint8_t x_585; 
x_319 = l_Lean_Syntax_getArg(x_272, x_80);
lean_dec(x_272);
x_320 = lean_unsigned_to_nat(4u);
x_321 = l_Lean_Syntax_getArg(x_1, x_320);
x_583 = l_Lean_nullKind___closed__2;
lean_inc(x_321);
x_584 = l_Lean_Syntax_isOfKind(x_321, x_583);
if (x_584 == 0)
{
uint8_t x_803; 
x_803 = 0;
x_585 = x_803;
goto block_802;
}
else
{
lean_object* x_804; lean_object* x_805; uint8_t x_806; 
x_804 = l_Lean_Syntax_getArgs(x_321);
x_805 = lean_array_get_size(x_804);
lean_dec(x_804);
x_806 = lean_nat_dec_eq(x_805, x_128);
lean_dec(x_805);
x_585 = x_806;
goto block_802;
}
block_582:
{
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_319);
lean_dec(x_223);
x_323 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = l_Lean_Elab_Term_getEnv___rarg(x_325);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_327, 2);
lean_inc(x_331);
x_332 = lean_ctor_get(x_327, 3);
lean_inc(x_332);
x_333 = lean_ctor_get(x_327, 4);
lean_inc(x_333);
x_334 = lean_ctor_get(x_327, 5);
lean_inc(x_334);
x_335 = lean_ctor_get(x_3, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_335, 3);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 4);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_environment_main_module(x_328);
x_339 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_324);
lean_ctor_set(x_339, 2, x_336);
lean_ctor_set(x_339, 3, x_337);
lean_inc(x_1);
x_340 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_339, x_334);
if (lean_obj_tag(x_340) == 0)
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_327);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = lean_ctor_get(x_327, 5);
lean_dec(x_342);
x_343 = lean_ctor_get(x_327, 4);
lean_dec(x_343);
x_344 = lean_ctor_get(x_327, 3);
lean_dec(x_344);
x_345 = lean_ctor_get(x_327, 2);
lean_dec(x_345);
x_346 = lean_ctor_get(x_327, 1);
lean_dec(x_346);
x_347 = lean_ctor_get(x_327, 0);
lean_dec(x_347);
x_348 = lean_ctor_get(x_340, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_340, 1);
lean_inc(x_349);
lean_dec(x_340);
lean_ctor_set(x_327, 5, x_349);
x_5 = x_348;
x_6 = x_327;
goto block_33;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_327);
x_350 = lean_ctor_get(x_340, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_340, 1);
lean_inc(x_351);
lean_dec(x_340);
x_352 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_352, 0, x_329);
lean_ctor_set(x_352, 1, x_330);
lean_ctor_set(x_352, 2, x_331);
lean_ctor_set(x_352, 3, x_332);
lean_ctor_set(x_352, 4, x_333);
lean_ctor_set(x_352, 5, x_351);
x_5 = x_350;
x_6 = x_352;
goto block_33;
}
}
else
{
lean_object* x_353; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_2);
lean_dec(x_1);
x_353 = lean_ctor_get(x_340, 0);
lean_inc(x_353);
lean_dec(x_340);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_357 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_358 = l_Lean_Elab_Term_throwErrorAt___rarg(x_354, x_357, x_3, x_327);
lean_dec(x_354);
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
return x_358;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_358, 0);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_358);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
else
{
lean_object* x_363; uint8_t x_364; 
lean_dec(x_3);
x_363 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_327);
x_364 = !lean_is_exclusive(x_363);
if (x_364 == 0)
{
return x_363;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_363, 0);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_363);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_576; uint8_t x_577; 
x_368 = lean_unsigned_to_nat(5u);
x_369 = l_Lean_Syntax_getArg(x_1, x_368);
x_576 = l_Lean_nullKind___closed__2;
lean_inc(x_369);
x_577 = l_Lean_Syntax_isOfKind(x_369, x_576);
if (x_577 == 0)
{
uint8_t x_578; 
x_578 = 0;
x_370 = x_578;
goto block_575;
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_579 = l_Lean_Syntax_getArgs(x_369);
x_580 = lean_array_get_size(x_579);
lean_dec(x_579);
x_581 = lean_nat_dec_eq(x_580, x_80);
lean_dec(x_580);
x_370 = x_581;
goto block_575;
}
block_575:
{
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_369);
lean_dec(x_319);
lean_dec(x_223);
x_371 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec(x_371);
x_374 = l_Lean_Elab_Term_getEnv___rarg(x_373);
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
x_380 = lean_ctor_get(x_375, 3);
lean_inc(x_380);
x_381 = lean_ctor_get(x_375, 4);
lean_inc(x_381);
x_382 = lean_ctor_get(x_375, 5);
lean_inc(x_382);
x_383 = lean_ctor_get(x_3, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_383, 3);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 4);
lean_inc(x_385);
lean_dec(x_383);
x_386 = lean_environment_main_module(x_376);
x_387 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_372);
lean_ctor_set(x_387, 2, x_384);
lean_ctor_set(x_387, 3, x_385);
lean_inc(x_1);
x_388 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_387, x_382);
if (lean_obj_tag(x_388) == 0)
{
uint8_t x_389; 
x_389 = !lean_is_exclusive(x_375);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_390 = lean_ctor_get(x_375, 5);
lean_dec(x_390);
x_391 = lean_ctor_get(x_375, 4);
lean_dec(x_391);
x_392 = lean_ctor_get(x_375, 3);
lean_dec(x_392);
x_393 = lean_ctor_get(x_375, 2);
lean_dec(x_393);
x_394 = lean_ctor_get(x_375, 1);
lean_dec(x_394);
x_395 = lean_ctor_get(x_375, 0);
lean_dec(x_395);
x_396 = lean_ctor_get(x_388, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_388, 1);
lean_inc(x_397);
lean_dec(x_388);
lean_ctor_set(x_375, 5, x_397);
x_5 = x_396;
x_6 = x_375;
goto block_33;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_375);
x_398 = lean_ctor_get(x_388, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_388, 1);
lean_inc(x_399);
lean_dec(x_388);
x_400 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_400, 0, x_377);
lean_ctor_set(x_400, 1, x_378);
lean_ctor_set(x_400, 2, x_379);
lean_ctor_set(x_400, 3, x_380);
lean_ctor_set(x_400, 4, x_381);
lean_ctor_set(x_400, 5, x_399);
x_5 = x_398;
x_6 = x_400;
goto block_33;
}
}
else
{
lean_object* x_401; 
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_379);
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_2);
lean_dec(x_1);
x_401 = lean_ctor_get(x_388, 0);
lean_inc(x_401);
lean_dec(x_388);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_404, 0, x_403);
x_405 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_406 = l_Lean_Elab_Term_throwErrorAt___rarg(x_402, x_405, x_3, x_375);
lean_dec(x_402);
x_407 = !lean_is_exclusive(x_406);
if (x_407 == 0)
{
return x_406;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_406, 0);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_406);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
else
{
lean_object* x_411; uint8_t x_412; 
lean_dec(x_3);
x_411 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_375);
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
return x_411;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_411, 0);
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_411);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
}
else
{
lean_object* x_416; uint8_t x_417; lean_object* x_568; uint8_t x_569; 
x_416 = l_Lean_Syntax_getArg(x_369, x_128);
lean_dec(x_369);
x_568 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_416);
x_569 = l_Lean_Syntax_isOfKind(x_416, x_568);
if (x_569 == 0)
{
uint8_t x_570; 
x_570 = 0;
x_417 = x_570;
goto block_567;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; 
x_571 = l_Lean_Syntax_getArgs(x_416);
x_572 = lean_array_get_size(x_571);
lean_dec(x_571);
x_573 = lean_unsigned_to_nat(3u);
x_574 = lean_nat_dec_eq(x_572, x_573);
lean_dec(x_572);
x_417 = x_574;
goto block_567;
}
block_567:
{
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_416);
lean_dec(x_319);
lean_dec(x_223);
x_418 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lean_Elab_Term_getEnv___rarg(x_420);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 0);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_422, 2);
lean_inc(x_426);
x_427 = lean_ctor_get(x_422, 3);
lean_inc(x_427);
x_428 = lean_ctor_get(x_422, 4);
lean_inc(x_428);
x_429 = lean_ctor_get(x_422, 5);
lean_inc(x_429);
x_430 = lean_ctor_get(x_3, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_430, 3);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 4);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_environment_main_module(x_423);
x_434 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_419);
lean_ctor_set(x_434, 2, x_431);
lean_ctor_set(x_434, 3, x_432);
lean_inc(x_1);
x_435 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_434, x_429);
if (lean_obj_tag(x_435) == 0)
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_422);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_437 = lean_ctor_get(x_422, 5);
lean_dec(x_437);
x_438 = lean_ctor_get(x_422, 4);
lean_dec(x_438);
x_439 = lean_ctor_get(x_422, 3);
lean_dec(x_439);
x_440 = lean_ctor_get(x_422, 2);
lean_dec(x_440);
x_441 = lean_ctor_get(x_422, 1);
lean_dec(x_441);
x_442 = lean_ctor_get(x_422, 0);
lean_dec(x_442);
x_443 = lean_ctor_get(x_435, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_435, 1);
lean_inc(x_444);
lean_dec(x_435);
lean_ctor_set(x_422, 5, x_444);
x_5 = x_443;
x_6 = x_422;
goto block_33;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_422);
x_445 = lean_ctor_get(x_435, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_435, 1);
lean_inc(x_446);
lean_dec(x_435);
x_447 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_447, 0, x_424);
lean_ctor_set(x_447, 1, x_425);
lean_ctor_set(x_447, 2, x_426);
lean_ctor_set(x_447, 3, x_427);
lean_ctor_set(x_447, 4, x_428);
lean_ctor_set(x_447, 5, x_446);
x_5 = x_445;
x_6 = x_447;
goto block_33;
}
}
else
{
lean_object* x_448; 
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_2);
lean_dec(x_1);
x_448 = lean_ctor_get(x_435, 0);
lean_inc(x_448);
lean_dec(x_435);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_451, 0, x_450);
x_452 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_452, 0, x_451);
x_453 = l_Lean_Elab_Term_throwErrorAt___rarg(x_449, x_452, x_3, x_422);
lean_dec(x_449);
x_454 = !lean_is_exclusive(x_453);
if (x_454 == 0)
{
return x_453;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_453, 0);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_453);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
else
{
lean_object* x_458; uint8_t x_459; 
lean_dec(x_3);
x_458 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_422);
x_459 = !lean_is_exclusive(x_458);
if (x_459 == 0)
{
return x_458;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_458, 0);
x_461 = lean_ctor_get(x_458, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_458);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
return x_462;
}
}
}
}
else
{
lean_object* x_463; uint8_t x_464; lean_object* x_561; uint8_t x_562; 
x_463 = l_Lean_Syntax_getArg(x_416, x_128);
x_561 = l_Lean_nullKind___closed__2;
lean_inc(x_463);
x_562 = l_Lean_Syntax_isOfKind(x_463, x_561);
if (x_562 == 0)
{
uint8_t x_563; 
x_563 = 0;
x_464 = x_563;
goto block_560;
}
else
{
lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_564 = l_Lean_Syntax_getArgs(x_463);
x_565 = lean_array_get_size(x_564);
lean_dec(x_564);
x_566 = lean_nat_dec_eq(x_565, x_80);
lean_dec(x_565);
x_464 = x_566;
goto block_560;
}
block_560:
{
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_463);
lean_dec(x_416);
lean_dec(x_319);
lean_dec(x_223);
x_465 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = l_Lean_Elab_Term_getEnv___rarg(x_467);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_469, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_469, 2);
lean_inc(x_473);
x_474 = lean_ctor_get(x_469, 3);
lean_inc(x_474);
x_475 = lean_ctor_get(x_469, 4);
lean_inc(x_475);
x_476 = lean_ctor_get(x_469, 5);
lean_inc(x_476);
x_477 = lean_ctor_get(x_3, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_477, 3);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 4);
lean_inc(x_479);
lean_dec(x_477);
x_480 = lean_environment_main_module(x_470);
x_481 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_466);
lean_ctor_set(x_481, 2, x_478);
lean_ctor_set(x_481, 3, x_479);
lean_inc(x_1);
x_482 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_481, x_476);
if (lean_obj_tag(x_482) == 0)
{
uint8_t x_483; 
x_483 = !lean_is_exclusive(x_469);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_484 = lean_ctor_get(x_469, 5);
lean_dec(x_484);
x_485 = lean_ctor_get(x_469, 4);
lean_dec(x_485);
x_486 = lean_ctor_get(x_469, 3);
lean_dec(x_486);
x_487 = lean_ctor_get(x_469, 2);
lean_dec(x_487);
x_488 = lean_ctor_get(x_469, 1);
lean_dec(x_488);
x_489 = lean_ctor_get(x_469, 0);
lean_dec(x_489);
x_490 = lean_ctor_get(x_482, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_482, 1);
lean_inc(x_491);
lean_dec(x_482);
lean_ctor_set(x_469, 5, x_491);
x_5 = x_490;
x_6 = x_469;
goto block_33;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_469);
x_492 = lean_ctor_get(x_482, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_482, 1);
lean_inc(x_493);
lean_dec(x_482);
x_494 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_494, 0, x_471);
lean_ctor_set(x_494, 1, x_472);
lean_ctor_set(x_494, 2, x_473);
lean_ctor_set(x_494, 3, x_474);
lean_ctor_set(x_494, 4, x_475);
lean_ctor_set(x_494, 5, x_493);
x_5 = x_492;
x_6 = x_494;
goto block_33;
}
}
else
{
lean_object* x_495; 
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_2);
lean_dec(x_1);
x_495 = lean_ctor_get(x_482, 0);
lean_inc(x_495);
lean_dec(x_482);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_498, 0, x_497);
x_499 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_499, 0, x_498);
x_500 = l_Lean_Elab_Term_throwErrorAt___rarg(x_496, x_499, x_3, x_469);
lean_dec(x_496);
x_501 = !lean_is_exclusive(x_500);
if (x_501 == 0)
{
return x_500;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_500, 0);
x_503 = lean_ctor_get(x_500, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_500);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
else
{
lean_object* x_505; uint8_t x_506; 
lean_dec(x_3);
x_505 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_469);
x_506 = !lean_is_exclusive(x_505);
if (x_506 == 0)
{
return x_505;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_505, 0);
x_508 = lean_ctor_get(x_505, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_505);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
}
else
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_510 = l_Lean_Syntax_getArg(x_463, x_128);
lean_dec(x_463);
x_511 = l_Lean_identKind___closed__2;
lean_inc(x_510);
x_512 = l_Lean_Syntax_isOfKind(x_510, x_511);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_510);
lean_dec(x_416);
lean_dec(x_319);
lean_dec(x_223);
x_513 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = l_Lean_Elab_Term_getEnv___rarg(x_515);
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
lean_dec(x_516);
x_519 = lean_ctor_get(x_517, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
x_521 = lean_ctor_get(x_517, 2);
lean_inc(x_521);
x_522 = lean_ctor_get(x_517, 3);
lean_inc(x_522);
x_523 = lean_ctor_get(x_517, 4);
lean_inc(x_523);
x_524 = lean_ctor_get(x_517, 5);
lean_inc(x_524);
x_525 = lean_ctor_get(x_3, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_525, 3);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 4);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_environment_main_module(x_518);
x_529 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_514);
lean_ctor_set(x_529, 2, x_526);
lean_ctor_set(x_529, 3, x_527);
lean_inc(x_1);
x_530 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_529, x_524);
if (lean_obj_tag(x_530) == 0)
{
uint8_t x_531; 
x_531 = !lean_is_exclusive(x_517);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_532 = lean_ctor_get(x_517, 5);
lean_dec(x_532);
x_533 = lean_ctor_get(x_517, 4);
lean_dec(x_533);
x_534 = lean_ctor_get(x_517, 3);
lean_dec(x_534);
x_535 = lean_ctor_get(x_517, 2);
lean_dec(x_535);
x_536 = lean_ctor_get(x_517, 1);
lean_dec(x_536);
x_537 = lean_ctor_get(x_517, 0);
lean_dec(x_537);
x_538 = lean_ctor_get(x_530, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_530, 1);
lean_inc(x_539);
lean_dec(x_530);
lean_ctor_set(x_517, 5, x_539);
x_5 = x_538;
x_6 = x_517;
goto block_33;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_517);
x_540 = lean_ctor_get(x_530, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_530, 1);
lean_inc(x_541);
lean_dec(x_530);
x_542 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_542, 0, x_519);
lean_ctor_set(x_542, 1, x_520);
lean_ctor_set(x_542, 2, x_521);
lean_ctor_set(x_542, 3, x_522);
lean_ctor_set(x_542, 4, x_523);
lean_ctor_set(x_542, 5, x_541);
x_5 = x_540;
x_6 = x_542;
goto block_33;
}
}
else
{
lean_object* x_543; 
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_2);
lean_dec(x_1);
x_543 = lean_ctor_get(x_530, 0);
lean_inc(x_543);
lean_dec(x_530);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_546, 0, x_545);
x_547 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_547, 0, x_546);
x_548 = l_Lean_Elab_Term_throwErrorAt___rarg(x_544, x_547, x_3, x_517);
lean_dec(x_544);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
return x_548;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_548);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
else
{
lean_object* x_553; uint8_t x_554; 
lean_dec(x_3);
x_553 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_517);
x_554 = !lean_is_exclusive(x_553);
if (x_554 == 0)
{
return x_553;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_553, 0);
x_556 = lean_ctor_get(x_553, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_553);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
}
else
{
lean_object* x_558; lean_object* x_559; 
x_558 = l_Lean_Syntax_getArg(x_416, x_224);
lean_dec(x_416);
x_559 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_223, x_510, x_319, x_558, x_2, x_3, x_4);
return x_559;
}
}
}
}
}
}
}
}
}
block_802:
{
if (x_585 == 0)
{
if (x_584 == 0)
{
uint8_t x_586; 
lean_dec(x_321);
x_586 = 0;
x_322 = x_586;
goto block_582;
}
else
{
lean_object* x_587; lean_object* x_588; uint8_t x_589; 
x_587 = l_Lean_Syntax_getArgs(x_321);
lean_dec(x_321);
x_588 = lean_array_get_size(x_587);
lean_dec(x_587);
x_589 = lean_nat_dec_eq(x_588, x_80);
lean_dec(x_588);
x_322 = x_589;
goto block_582;
}
}
else
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; uint8_t x_797; 
lean_dec(x_321);
x_590 = lean_unsigned_to_nat(5u);
x_591 = l_Lean_Syntax_getArg(x_1, x_590);
lean_inc(x_591);
x_797 = l_Lean_Syntax_isOfKind(x_591, x_583);
if (x_797 == 0)
{
uint8_t x_798; 
x_798 = 0;
x_592 = x_798;
goto block_796;
}
else
{
lean_object* x_799; lean_object* x_800; uint8_t x_801; 
x_799 = l_Lean_Syntax_getArgs(x_591);
x_800 = lean_array_get_size(x_799);
lean_dec(x_799);
x_801 = lean_nat_dec_eq(x_800, x_80);
lean_dec(x_800);
x_592 = x_801;
goto block_796;
}
block_796:
{
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_591);
lean_dec(x_319);
lean_dec(x_223);
x_593 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec(x_593);
x_596 = l_Lean_Elab_Term_getEnv___rarg(x_595);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
lean_dec(x_596);
x_599 = lean_ctor_get(x_597, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_597, 1);
lean_inc(x_600);
x_601 = lean_ctor_get(x_597, 2);
lean_inc(x_601);
x_602 = lean_ctor_get(x_597, 3);
lean_inc(x_602);
x_603 = lean_ctor_get(x_597, 4);
lean_inc(x_603);
x_604 = lean_ctor_get(x_597, 5);
lean_inc(x_604);
x_605 = lean_ctor_get(x_3, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_605, 3);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 4);
lean_inc(x_607);
lean_dec(x_605);
x_608 = lean_environment_main_module(x_598);
x_609 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_594);
lean_ctor_set(x_609, 2, x_606);
lean_ctor_set(x_609, 3, x_607);
lean_inc(x_1);
x_610 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_609, x_604);
if (lean_obj_tag(x_610) == 0)
{
uint8_t x_611; 
x_611 = !lean_is_exclusive(x_597);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_612 = lean_ctor_get(x_597, 5);
lean_dec(x_612);
x_613 = lean_ctor_get(x_597, 4);
lean_dec(x_613);
x_614 = lean_ctor_get(x_597, 3);
lean_dec(x_614);
x_615 = lean_ctor_get(x_597, 2);
lean_dec(x_615);
x_616 = lean_ctor_get(x_597, 1);
lean_dec(x_616);
x_617 = lean_ctor_get(x_597, 0);
lean_dec(x_617);
x_618 = lean_ctor_get(x_610, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_610, 1);
lean_inc(x_619);
lean_dec(x_610);
lean_ctor_set(x_597, 5, x_619);
x_5 = x_618;
x_6 = x_597;
goto block_33;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_597);
x_620 = lean_ctor_get(x_610, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_610, 1);
lean_inc(x_621);
lean_dec(x_610);
x_622 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_622, 0, x_599);
lean_ctor_set(x_622, 1, x_600);
lean_ctor_set(x_622, 2, x_601);
lean_ctor_set(x_622, 3, x_602);
lean_ctor_set(x_622, 4, x_603);
lean_ctor_set(x_622, 5, x_621);
x_5 = x_620;
x_6 = x_622;
goto block_33;
}
}
else
{
lean_object* x_623; 
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_2);
lean_dec(x_1);
x_623 = lean_ctor_get(x_610, 0);
lean_inc(x_623);
lean_dec(x_610);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_626, 0, x_625);
x_627 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_627, 0, x_626);
x_628 = l_Lean_Elab_Term_throwErrorAt___rarg(x_624, x_627, x_3, x_597);
lean_dec(x_624);
x_629 = !lean_is_exclusive(x_628);
if (x_629 == 0)
{
return x_628;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_628, 0);
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_628);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
}
else
{
lean_object* x_633; uint8_t x_634; 
lean_dec(x_3);
x_633 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_597);
x_634 = !lean_is_exclusive(x_633);
if (x_634 == 0)
{
return x_633;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_633, 0);
x_636 = lean_ctor_get(x_633, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_633);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
}
else
{
lean_object* x_638; uint8_t x_639; lean_object* x_789; uint8_t x_790; 
x_638 = l_Lean_Syntax_getArg(x_591, x_128);
lean_dec(x_591);
x_789 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_638);
x_790 = l_Lean_Syntax_isOfKind(x_638, x_789);
if (x_790 == 0)
{
uint8_t x_791; 
x_791 = 0;
x_639 = x_791;
goto block_788;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; uint8_t x_795; 
x_792 = l_Lean_Syntax_getArgs(x_638);
x_793 = lean_array_get_size(x_792);
lean_dec(x_792);
x_794 = lean_unsigned_to_nat(3u);
x_795 = lean_nat_dec_eq(x_793, x_794);
lean_dec(x_793);
x_639 = x_795;
goto block_788;
}
block_788:
{
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_638);
lean_dec(x_319);
lean_dec(x_223);
x_640 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = l_Lean_Elab_Term_getEnv___rarg(x_642);
x_644 = lean_ctor_get(x_643, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 0);
lean_inc(x_645);
lean_dec(x_643);
x_646 = lean_ctor_get(x_644, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_644, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_644, 2);
lean_inc(x_648);
x_649 = lean_ctor_get(x_644, 3);
lean_inc(x_649);
x_650 = lean_ctor_get(x_644, 4);
lean_inc(x_650);
x_651 = lean_ctor_get(x_644, 5);
lean_inc(x_651);
x_652 = lean_ctor_get(x_3, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_652, 3);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 4);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_environment_main_module(x_645);
x_656 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_641);
lean_ctor_set(x_656, 2, x_653);
lean_ctor_set(x_656, 3, x_654);
lean_inc(x_1);
x_657 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_656, x_651);
if (lean_obj_tag(x_657) == 0)
{
uint8_t x_658; 
x_658 = !lean_is_exclusive(x_644);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_659 = lean_ctor_get(x_644, 5);
lean_dec(x_659);
x_660 = lean_ctor_get(x_644, 4);
lean_dec(x_660);
x_661 = lean_ctor_get(x_644, 3);
lean_dec(x_661);
x_662 = lean_ctor_get(x_644, 2);
lean_dec(x_662);
x_663 = lean_ctor_get(x_644, 1);
lean_dec(x_663);
x_664 = lean_ctor_get(x_644, 0);
lean_dec(x_664);
x_665 = lean_ctor_get(x_657, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_657, 1);
lean_inc(x_666);
lean_dec(x_657);
lean_ctor_set(x_644, 5, x_666);
x_5 = x_665;
x_6 = x_644;
goto block_33;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_644);
x_667 = lean_ctor_get(x_657, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_657, 1);
lean_inc(x_668);
lean_dec(x_657);
x_669 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_669, 0, x_646);
lean_ctor_set(x_669, 1, x_647);
lean_ctor_set(x_669, 2, x_648);
lean_ctor_set(x_669, 3, x_649);
lean_ctor_set(x_669, 4, x_650);
lean_ctor_set(x_669, 5, x_668);
x_5 = x_667;
x_6 = x_669;
goto block_33;
}
}
else
{
lean_object* x_670; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_646);
lean_dec(x_2);
lean_dec(x_1);
x_670 = lean_ctor_get(x_657, 0);
lean_inc(x_670);
lean_dec(x_657);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
x_673 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_673, 0, x_672);
x_674 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_674, 0, x_673);
x_675 = l_Lean_Elab_Term_throwErrorAt___rarg(x_671, x_674, x_3, x_644);
lean_dec(x_671);
x_676 = !lean_is_exclusive(x_675);
if (x_676 == 0)
{
return x_675;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_675, 0);
x_678 = lean_ctor_get(x_675, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_675);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
else
{
lean_object* x_680; uint8_t x_681; 
lean_dec(x_3);
x_680 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_644);
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
return x_680;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_ctor_get(x_680, 0);
x_683 = lean_ctor_get(x_680, 1);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_680);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_682);
lean_ctor_set(x_684, 1, x_683);
return x_684;
}
}
}
}
else
{
lean_object* x_685; uint8_t x_686; uint8_t x_783; 
x_685 = l_Lean_Syntax_getArg(x_638, x_128);
lean_inc(x_685);
x_783 = l_Lean_Syntax_isOfKind(x_685, x_583);
if (x_783 == 0)
{
uint8_t x_784; 
x_784 = 0;
x_686 = x_784;
goto block_782;
}
else
{
lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_785 = l_Lean_Syntax_getArgs(x_685);
x_786 = lean_array_get_size(x_785);
lean_dec(x_785);
x_787 = lean_nat_dec_eq(x_786, x_80);
lean_dec(x_786);
x_686 = x_787;
goto block_782;
}
block_782:
{
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_685);
lean_dec(x_638);
lean_dec(x_319);
lean_dec(x_223);
x_687 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
x_690 = l_Lean_Elab_Term_getEnv___rarg(x_689);
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 0);
lean_inc(x_692);
lean_dec(x_690);
x_693 = lean_ctor_get(x_691, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_691, 1);
lean_inc(x_694);
x_695 = lean_ctor_get(x_691, 2);
lean_inc(x_695);
x_696 = lean_ctor_get(x_691, 3);
lean_inc(x_696);
x_697 = lean_ctor_get(x_691, 4);
lean_inc(x_697);
x_698 = lean_ctor_get(x_691, 5);
lean_inc(x_698);
x_699 = lean_ctor_get(x_3, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_699, 3);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 4);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_environment_main_module(x_692);
x_703 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_688);
lean_ctor_set(x_703, 2, x_700);
lean_ctor_set(x_703, 3, x_701);
lean_inc(x_1);
x_704 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_703, x_698);
if (lean_obj_tag(x_704) == 0)
{
uint8_t x_705; 
x_705 = !lean_is_exclusive(x_691);
if (x_705 == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_706 = lean_ctor_get(x_691, 5);
lean_dec(x_706);
x_707 = lean_ctor_get(x_691, 4);
lean_dec(x_707);
x_708 = lean_ctor_get(x_691, 3);
lean_dec(x_708);
x_709 = lean_ctor_get(x_691, 2);
lean_dec(x_709);
x_710 = lean_ctor_get(x_691, 1);
lean_dec(x_710);
x_711 = lean_ctor_get(x_691, 0);
lean_dec(x_711);
x_712 = lean_ctor_get(x_704, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_704, 1);
lean_inc(x_713);
lean_dec(x_704);
lean_ctor_set(x_691, 5, x_713);
x_5 = x_712;
x_6 = x_691;
goto block_33;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_691);
x_714 = lean_ctor_get(x_704, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_704, 1);
lean_inc(x_715);
lean_dec(x_704);
x_716 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_716, 0, x_693);
lean_ctor_set(x_716, 1, x_694);
lean_ctor_set(x_716, 2, x_695);
lean_ctor_set(x_716, 3, x_696);
lean_ctor_set(x_716, 4, x_697);
lean_ctor_set(x_716, 5, x_715);
x_5 = x_714;
x_6 = x_716;
goto block_33;
}
}
else
{
lean_object* x_717; 
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_694);
lean_dec(x_693);
lean_dec(x_2);
lean_dec(x_1);
x_717 = lean_ctor_get(x_704, 0);
lean_inc(x_717);
lean_dec(x_704);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; uint8_t x_723; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_720, 0, x_719);
x_721 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_721, 0, x_720);
x_722 = l_Lean_Elab_Term_throwErrorAt___rarg(x_718, x_721, x_3, x_691);
lean_dec(x_718);
x_723 = !lean_is_exclusive(x_722);
if (x_723 == 0)
{
return x_722;
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_ctor_get(x_722, 0);
x_725 = lean_ctor_get(x_722, 1);
lean_inc(x_725);
lean_inc(x_724);
lean_dec(x_722);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_724);
lean_ctor_set(x_726, 1, x_725);
return x_726;
}
}
else
{
lean_object* x_727; uint8_t x_728; 
lean_dec(x_3);
x_727 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_691);
x_728 = !lean_is_exclusive(x_727);
if (x_728 == 0)
{
return x_727;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_727, 0);
x_730 = lean_ctor_get(x_727, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_727);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
}
else
{
lean_object* x_732; lean_object* x_733; uint8_t x_734; 
x_732 = l_Lean_Syntax_getArg(x_685, x_128);
lean_dec(x_685);
x_733 = l_Lean_identKind___closed__2;
lean_inc(x_732);
x_734 = l_Lean_Syntax_isOfKind(x_732, x_733);
if (x_734 == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_732);
lean_dec(x_638);
lean_dec(x_319);
lean_dec(x_223);
x_735 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
x_738 = l_Lean_Elab_Term_getEnv___rarg(x_737);
x_739 = lean_ctor_get(x_738, 1);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 0);
lean_inc(x_740);
lean_dec(x_738);
x_741 = lean_ctor_get(x_739, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_739, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_739, 2);
lean_inc(x_743);
x_744 = lean_ctor_get(x_739, 3);
lean_inc(x_744);
x_745 = lean_ctor_get(x_739, 4);
lean_inc(x_745);
x_746 = lean_ctor_get(x_739, 5);
lean_inc(x_746);
x_747 = lean_ctor_get(x_3, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_747, 3);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 4);
lean_inc(x_749);
lean_dec(x_747);
x_750 = lean_environment_main_module(x_740);
x_751 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set(x_751, 1, x_736);
lean_ctor_set(x_751, 2, x_748);
lean_ctor_set(x_751, 3, x_749);
lean_inc(x_1);
x_752 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_751, x_746);
if (lean_obj_tag(x_752) == 0)
{
uint8_t x_753; 
x_753 = !lean_is_exclusive(x_739);
if (x_753 == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_754 = lean_ctor_get(x_739, 5);
lean_dec(x_754);
x_755 = lean_ctor_get(x_739, 4);
lean_dec(x_755);
x_756 = lean_ctor_get(x_739, 3);
lean_dec(x_756);
x_757 = lean_ctor_get(x_739, 2);
lean_dec(x_757);
x_758 = lean_ctor_get(x_739, 1);
lean_dec(x_758);
x_759 = lean_ctor_get(x_739, 0);
lean_dec(x_759);
x_760 = lean_ctor_get(x_752, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_752, 1);
lean_inc(x_761);
lean_dec(x_752);
lean_ctor_set(x_739, 5, x_761);
x_5 = x_760;
x_6 = x_739;
goto block_33;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_739);
x_762 = lean_ctor_get(x_752, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_752, 1);
lean_inc(x_763);
lean_dec(x_752);
x_764 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_764, 0, x_741);
lean_ctor_set(x_764, 1, x_742);
lean_ctor_set(x_764, 2, x_743);
lean_ctor_set(x_764, 3, x_744);
lean_ctor_set(x_764, 4, x_745);
lean_ctor_set(x_764, 5, x_763);
x_5 = x_762;
x_6 = x_764;
goto block_33;
}
}
else
{
lean_object* x_765; 
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_741);
lean_dec(x_2);
lean_dec(x_1);
x_765 = lean_ctor_get(x_752, 0);
lean_inc(x_765);
lean_dec(x_752);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
lean_dec(x_765);
x_768 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_768, 0, x_767);
x_769 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_769, 0, x_768);
x_770 = l_Lean_Elab_Term_throwErrorAt___rarg(x_766, x_769, x_3, x_739);
lean_dec(x_766);
x_771 = !lean_is_exclusive(x_770);
if (x_771 == 0)
{
return x_770;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_770, 0);
x_773 = lean_ctor_get(x_770, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_770);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
else
{
lean_object* x_775; uint8_t x_776; 
lean_dec(x_3);
x_775 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_739);
x_776 = !lean_is_exclusive(x_775);
if (x_776 == 0)
{
return x_775;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_ctor_get(x_775, 0);
x_778 = lean_ctor_get(x_775, 1);
lean_inc(x_778);
lean_inc(x_777);
lean_dec(x_775);
x_779 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_779, 0, x_777);
lean_ctor_set(x_779, 1, x_778);
return x_779;
}
}
}
}
else
{
lean_object* x_780; lean_object* x_781; 
x_780 = l_Lean_Syntax_getArg(x_638, x_224);
lean_dec(x_638);
x_781 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_223, x_732, x_319, x_780, x_2, x_3, x_4);
return x_781;
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
block_1306:
{
if (x_817 == 0)
{
if (x_816 == 0)
{
uint8_t x_818; 
x_818 = 0;
x_226 = x_818;
goto block_814;
}
else
{
lean_object* x_819; lean_object* x_820; uint8_t x_821; 
x_819 = l_Lean_Syntax_getArgs(x_225);
x_820 = lean_array_get_size(x_819);
lean_dec(x_819);
x_821 = lean_nat_dec_eq(x_820, x_80);
lean_dec(x_820);
x_226 = x_821;
goto block_814;
}
}
else
{
lean_object* x_822; lean_object* x_823; uint8_t x_824; uint8_t x_1083; uint8_t x_1084; 
lean_dec(x_225);
x_822 = lean_unsigned_to_nat(4u);
x_823 = l_Lean_Syntax_getArg(x_1, x_822);
lean_inc(x_823);
x_1083 = l_Lean_Syntax_isOfKind(x_823, x_815);
if (x_1083 == 0)
{
uint8_t x_1302; 
x_1302 = 0;
x_1084 = x_1302;
goto block_1301;
}
else
{
lean_object* x_1303; lean_object* x_1304; uint8_t x_1305; 
x_1303 = l_Lean_Syntax_getArgs(x_823);
x_1304 = lean_array_get_size(x_1303);
lean_dec(x_1303);
x_1305 = lean_nat_dec_eq(x_1304, x_128);
lean_dec(x_1304);
x_1084 = x_1305;
goto block_1301;
}
block_1082:
{
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_223);
x_825 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = l_Lean_Elab_Term_getEnv___rarg(x_827);
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 0);
lean_inc(x_830);
lean_dec(x_828);
x_831 = lean_ctor_get(x_829, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_829, 1);
lean_inc(x_832);
x_833 = lean_ctor_get(x_829, 2);
lean_inc(x_833);
x_834 = lean_ctor_get(x_829, 3);
lean_inc(x_834);
x_835 = lean_ctor_get(x_829, 4);
lean_inc(x_835);
x_836 = lean_ctor_get(x_829, 5);
lean_inc(x_836);
x_837 = lean_ctor_get(x_3, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_837, 3);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 4);
lean_inc(x_839);
lean_dec(x_837);
x_840 = lean_environment_main_module(x_830);
x_841 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_826);
lean_ctor_set(x_841, 2, x_838);
lean_ctor_set(x_841, 3, x_839);
lean_inc(x_1);
x_842 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_841, x_836);
if (lean_obj_tag(x_842) == 0)
{
uint8_t x_843; 
x_843 = !lean_is_exclusive(x_829);
if (x_843 == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_844 = lean_ctor_get(x_829, 5);
lean_dec(x_844);
x_845 = lean_ctor_get(x_829, 4);
lean_dec(x_845);
x_846 = lean_ctor_get(x_829, 3);
lean_dec(x_846);
x_847 = lean_ctor_get(x_829, 2);
lean_dec(x_847);
x_848 = lean_ctor_get(x_829, 1);
lean_dec(x_848);
x_849 = lean_ctor_get(x_829, 0);
lean_dec(x_849);
x_850 = lean_ctor_get(x_842, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_842, 1);
lean_inc(x_851);
lean_dec(x_842);
lean_ctor_set(x_829, 5, x_851);
x_5 = x_850;
x_6 = x_829;
goto block_33;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_829);
x_852 = lean_ctor_get(x_842, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_842, 1);
lean_inc(x_853);
lean_dec(x_842);
x_854 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_854, 0, x_831);
lean_ctor_set(x_854, 1, x_832);
lean_ctor_set(x_854, 2, x_833);
lean_ctor_set(x_854, 3, x_834);
lean_ctor_set(x_854, 4, x_835);
lean_ctor_set(x_854, 5, x_853);
x_5 = x_852;
x_6 = x_854;
goto block_33;
}
}
else
{
lean_object* x_855; 
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_831);
lean_dec(x_2);
lean_dec(x_1);
x_855 = lean_ctor_get(x_842, 0);
lean_inc(x_855);
lean_dec(x_842);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; uint8_t x_861; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
lean_dec(x_855);
x_858 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_858, 0, x_857);
x_859 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_859, 0, x_858);
x_860 = l_Lean_Elab_Term_throwErrorAt___rarg(x_856, x_859, x_3, x_829);
lean_dec(x_856);
x_861 = !lean_is_exclusive(x_860);
if (x_861 == 0)
{
return x_860;
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_862 = lean_ctor_get(x_860, 0);
x_863 = lean_ctor_get(x_860, 1);
lean_inc(x_863);
lean_inc(x_862);
lean_dec(x_860);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_862);
lean_ctor_set(x_864, 1, x_863);
return x_864;
}
}
else
{
lean_object* x_865; uint8_t x_866; 
lean_dec(x_3);
x_865 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_829);
x_866 = !lean_is_exclusive(x_865);
if (x_866 == 0)
{
return x_865;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_867 = lean_ctor_get(x_865, 0);
x_868 = lean_ctor_get(x_865, 1);
lean_inc(x_868);
lean_inc(x_867);
lean_dec(x_865);
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_868);
return x_869;
}
}
}
}
else
{
lean_object* x_870; lean_object* x_871; uint8_t x_872; uint8_t x_1077; 
x_870 = lean_unsigned_to_nat(5u);
x_871 = l_Lean_Syntax_getArg(x_1, x_870);
lean_inc(x_871);
x_1077 = l_Lean_Syntax_isOfKind(x_871, x_815);
if (x_1077 == 0)
{
uint8_t x_1078; 
x_1078 = 0;
x_872 = x_1078;
goto block_1076;
}
else
{
lean_object* x_1079; lean_object* x_1080; uint8_t x_1081; 
x_1079 = l_Lean_Syntax_getArgs(x_871);
x_1080 = lean_array_get_size(x_1079);
lean_dec(x_1079);
x_1081 = lean_nat_dec_eq(x_1080, x_80);
lean_dec(x_1080);
x_872 = x_1081;
goto block_1076;
}
block_1076:
{
if (x_872 == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_871);
lean_dec(x_223);
x_873 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_876 = l_Lean_Elab_Term_getEnv___rarg(x_875);
x_877 = lean_ctor_get(x_876, 1);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec(x_876);
x_879 = lean_ctor_get(x_877, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_877, 1);
lean_inc(x_880);
x_881 = lean_ctor_get(x_877, 2);
lean_inc(x_881);
x_882 = lean_ctor_get(x_877, 3);
lean_inc(x_882);
x_883 = lean_ctor_get(x_877, 4);
lean_inc(x_883);
x_884 = lean_ctor_get(x_877, 5);
lean_inc(x_884);
x_885 = lean_ctor_get(x_3, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_885, 3);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 4);
lean_inc(x_887);
lean_dec(x_885);
x_888 = lean_environment_main_module(x_878);
x_889 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_874);
lean_ctor_set(x_889, 2, x_886);
lean_ctor_set(x_889, 3, x_887);
lean_inc(x_1);
x_890 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_889, x_884);
if (lean_obj_tag(x_890) == 0)
{
uint8_t x_891; 
x_891 = !lean_is_exclusive(x_877);
if (x_891 == 0)
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_892 = lean_ctor_get(x_877, 5);
lean_dec(x_892);
x_893 = lean_ctor_get(x_877, 4);
lean_dec(x_893);
x_894 = lean_ctor_get(x_877, 3);
lean_dec(x_894);
x_895 = lean_ctor_get(x_877, 2);
lean_dec(x_895);
x_896 = lean_ctor_get(x_877, 1);
lean_dec(x_896);
x_897 = lean_ctor_get(x_877, 0);
lean_dec(x_897);
x_898 = lean_ctor_get(x_890, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_890, 1);
lean_inc(x_899);
lean_dec(x_890);
lean_ctor_set(x_877, 5, x_899);
x_5 = x_898;
x_6 = x_877;
goto block_33;
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_877);
x_900 = lean_ctor_get(x_890, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_890, 1);
lean_inc(x_901);
lean_dec(x_890);
x_902 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_902, 0, x_879);
lean_ctor_set(x_902, 1, x_880);
lean_ctor_set(x_902, 2, x_881);
lean_ctor_set(x_902, 3, x_882);
lean_ctor_set(x_902, 4, x_883);
lean_ctor_set(x_902, 5, x_901);
x_5 = x_900;
x_6 = x_902;
goto block_33;
}
}
else
{
lean_object* x_903; 
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_880);
lean_dec(x_879);
lean_dec(x_2);
lean_dec(x_1);
x_903 = lean_ctor_get(x_890, 0);
lean_inc(x_903);
lean_dec(x_890);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; uint8_t x_909; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_903, 1);
lean_inc(x_905);
lean_dec(x_903);
x_906 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_906, 0, x_905);
x_907 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_907, 0, x_906);
x_908 = l_Lean_Elab_Term_throwErrorAt___rarg(x_904, x_907, x_3, x_877);
lean_dec(x_904);
x_909 = !lean_is_exclusive(x_908);
if (x_909 == 0)
{
return x_908;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; 
x_910 = lean_ctor_get(x_908, 0);
x_911 = lean_ctor_get(x_908, 1);
lean_inc(x_911);
lean_inc(x_910);
lean_dec(x_908);
x_912 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_912, 0, x_910);
lean_ctor_set(x_912, 1, x_911);
return x_912;
}
}
else
{
lean_object* x_913; uint8_t x_914; 
lean_dec(x_3);
x_913 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_877);
x_914 = !lean_is_exclusive(x_913);
if (x_914 == 0)
{
return x_913;
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_915 = lean_ctor_get(x_913, 0);
x_916 = lean_ctor_get(x_913, 1);
lean_inc(x_916);
lean_inc(x_915);
lean_dec(x_913);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_915);
lean_ctor_set(x_917, 1, x_916);
return x_917;
}
}
}
}
else
{
lean_object* x_918; uint8_t x_919; lean_object* x_1069; uint8_t x_1070; 
x_918 = l_Lean_Syntax_getArg(x_871, x_128);
lean_dec(x_871);
x_1069 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_918);
x_1070 = l_Lean_Syntax_isOfKind(x_918, x_1069);
if (x_1070 == 0)
{
uint8_t x_1071; 
x_1071 = 0;
x_919 = x_1071;
goto block_1068;
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; uint8_t x_1075; 
x_1072 = l_Lean_Syntax_getArgs(x_918);
x_1073 = lean_array_get_size(x_1072);
lean_dec(x_1072);
x_1074 = lean_unsigned_to_nat(3u);
x_1075 = lean_nat_dec_eq(x_1073, x_1074);
lean_dec(x_1073);
x_919 = x_1075;
goto block_1068;
}
block_1068:
{
if (x_919 == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
lean_dec(x_918);
lean_dec(x_223);
x_920 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
lean_dec(x_920);
x_923 = l_Lean_Elab_Term_getEnv___rarg(x_922);
x_924 = lean_ctor_get(x_923, 1);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 0);
lean_inc(x_925);
lean_dec(x_923);
x_926 = lean_ctor_get(x_924, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_924, 1);
lean_inc(x_927);
x_928 = lean_ctor_get(x_924, 2);
lean_inc(x_928);
x_929 = lean_ctor_get(x_924, 3);
lean_inc(x_929);
x_930 = lean_ctor_get(x_924, 4);
lean_inc(x_930);
x_931 = lean_ctor_get(x_924, 5);
lean_inc(x_931);
x_932 = lean_ctor_get(x_3, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_932, 3);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 4);
lean_inc(x_934);
lean_dec(x_932);
x_935 = lean_environment_main_module(x_925);
x_936 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_936, 0, x_935);
lean_ctor_set(x_936, 1, x_921);
lean_ctor_set(x_936, 2, x_933);
lean_ctor_set(x_936, 3, x_934);
lean_inc(x_1);
x_937 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_936, x_931);
if (lean_obj_tag(x_937) == 0)
{
uint8_t x_938; 
x_938 = !lean_is_exclusive(x_924);
if (x_938 == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_939 = lean_ctor_get(x_924, 5);
lean_dec(x_939);
x_940 = lean_ctor_get(x_924, 4);
lean_dec(x_940);
x_941 = lean_ctor_get(x_924, 3);
lean_dec(x_941);
x_942 = lean_ctor_get(x_924, 2);
lean_dec(x_942);
x_943 = lean_ctor_get(x_924, 1);
lean_dec(x_943);
x_944 = lean_ctor_get(x_924, 0);
lean_dec(x_944);
x_945 = lean_ctor_get(x_937, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_937, 1);
lean_inc(x_946);
lean_dec(x_937);
lean_ctor_set(x_924, 5, x_946);
x_5 = x_945;
x_6 = x_924;
goto block_33;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec(x_924);
x_947 = lean_ctor_get(x_937, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_937, 1);
lean_inc(x_948);
lean_dec(x_937);
x_949 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_949, 0, x_926);
lean_ctor_set(x_949, 1, x_927);
lean_ctor_set(x_949, 2, x_928);
lean_ctor_set(x_949, 3, x_929);
lean_ctor_set(x_949, 4, x_930);
lean_ctor_set(x_949, 5, x_948);
x_5 = x_947;
x_6 = x_949;
goto block_33;
}
}
else
{
lean_object* x_950; 
lean_dec(x_930);
lean_dec(x_929);
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_926);
lean_dec(x_2);
lean_dec(x_1);
x_950 = lean_ctor_get(x_937, 0);
lean_inc(x_950);
lean_dec(x_937);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; uint8_t x_956; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
lean_dec(x_950);
x_953 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_953, 0, x_952);
x_954 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_954, 0, x_953);
x_955 = l_Lean_Elab_Term_throwErrorAt___rarg(x_951, x_954, x_3, x_924);
lean_dec(x_951);
x_956 = !lean_is_exclusive(x_955);
if (x_956 == 0)
{
return x_955;
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_957 = lean_ctor_get(x_955, 0);
x_958 = lean_ctor_get(x_955, 1);
lean_inc(x_958);
lean_inc(x_957);
lean_dec(x_955);
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_957);
lean_ctor_set(x_959, 1, x_958);
return x_959;
}
}
else
{
lean_object* x_960; uint8_t x_961; 
lean_dec(x_3);
x_960 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_924);
x_961 = !lean_is_exclusive(x_960);
if (x_961 == 0)
{
return x_960;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_960, 0);
x_963 = lean_ctor_get(x_960, 1);
lean_inc(x_963);
lean_inc(x_962);
lean_dec(x_960);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set(x_964, 1, x_963);
return x_964;
}
}
}
}
else
{
lean_object* x_965; uint8_t x_966; uint8_t x_1063; 
x_965 = l_Lean_Syntax_getArg(x_918, x_128);
lean_inc(x_965);
x_1063 = l_Lean_Syntax_isOfKind(x_965, x_815);
if (x_1063 == 0)
{
uint8_t x_1064; 
x_1064 = 0;
x_966 = x_1064;
goto block_1062;
}
else
{
lean_object* x_1065; lean_object* x_1066; uint8_t x_1067; 
x_1065 = l_Lean_Syntax_getArgs(x_965);
x_1066 = lean_array_get_size(x_1065);
lean_dec(x_1065);
x_1067 = lean_nat_dec_eq(x_1066, x_80);
lean_dec(x_1066);
x_966 = x_1067;
goto block_1062;
}
block_1062:
{
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_965);
lean_dec(x_918);
lean_dec(x_223);
x_967 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
lean_dec(x_967);
x_970 = l_Lean_Elab_Term_getEnv___rarg(x_969);
x_971 = lean_ctor_get(x_970, 1);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 0);
lean_inc(x_972);
lean_dec(x_970);
x_973 = lean_ctor_get(x_971, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_971, 1);
lean_inc(x_974);
x_975 = lean_ctor_get(x_971, 2);
lean_inc(x_975);
x_976 = lean_ctor_get(x_971, 3);
lean_inc(x_976);
x_977 = lean_ctor_get(x_971, 4);
lean_inc(x_977);
x_978 = lean_ctor_get(x_971, 5);
lean_inc(x_978);
x_979 = lean_ctor_get(x_3, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_979, 3);
lean_inc(x_980);
x_981 = lean_ctor_get(x_979, 4);
lean_inc(x_981);
lean_dec(x_979);
x_982 = lean_environment_main_module(x_972);
x_983 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_968);
lean_ctor_set(x_983, 2, x_980);
lean_ctor_set(x_983, 3, x_981);
lean_inc(x_1);
x_984 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_983, x_978);
if (lean_obj_tag(x_984) == 0)
{
uint8_t x_985; 
x_985 = !lean_is_exclusive(x_971);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_986 = lean_ctor_get(x_971, 5);
lean_dec(x_986);
x_987 = lean_ctor_get(x_971, 4);
lean_dec(x_987);
x_988 = lean_ctor_get(x_971, 3);
lean_dec(x_988);
x_989 = lean_ctor_get(x_971, 2);
lean_dec(x_989);
x_990 = lean_ctor_get(x_971, 1);
lean_dec(x_990);
x_991 = lean_ctor_get(x_971, 0);
lean_dec(x_991);
x_992 = lean_ctor_get(x_984, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_984, 1);
lean_inc(x_993);
lean_dec(x_984);
lean_ctor_set(x_971, 5, x_993);
x_5 = x_992;
x_6 = x_971;
goto block_33;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
lean_dec(x_971);
x_994 = lean_ctor_get(x_984, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_984, 1);
lean_inc(x_995);
lean_dec(x_984);
x_996 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_996, 0, x_973);
lean_ctor_set(x_996, 1, x_974);
lean_ctor_set(x_996, 2, x_975);
lean_ctor_set(x_996, 3, x_976);
lean_ctor_set(x_996, 4, x_977);
lean_ctor_set(x_996, 5, x_995);
x_5 = x_994;
x_6 = x_996;
goto block_33;
}
}
else
{
lean_object* x_997; 
lean_dec(x_977);
lean_dec(x_976);
lean_dec(x_975);
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_2);
lean_dec(x_1);
x_997 = lean_ctor_get(x_984, 0);
lean_inc(x_997);
lean_dec(x_984);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
lean_dec(x_997);
x_1000 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1000, 0, x_999);
x_1001 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1001, 0, x_1000);
x_1002 = l_Lean_Elab_Term_throwErrorAt___rarg(x_998, x_1001, x_3, x_971);
lean_dec(x_998);
x_1003 = !lean_is_exclusive(x_1002);
if (x_1003 == 0)
{
return x_1002;
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1004 = lean_ctor_get(x_1002, 0);
x_1005 = lean_ctor_get(x_1002, 1);
lean_inc(x_1005);
lean_inc(x_1004);
lean_dec(x_1002);
x_1006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1006, 0, x_1004);
lean_ctor_set(x_1006, 1, x_1005);
return x_1006;
}
}
else
{
lean_object* x_1007; uint8_t x_1008; 
lean_dec(x_3);
x_1007 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_971);
x_1008 = !lean_is_exclusive(x_1007);
if (x_1008 == 0)
{
return x_1007;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_1007, 0);
x_1010 = lean_ctor_get(x_1007, 1);
lean_inc(x_1010);
lean_inc(x_1009);
lean_dec(x_1007);
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_1010);
return x_1011;
}
}
}
}
else
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; 
x_1012 = l_Lean_Syntax_getArg(x_965, x_128);
lean_dec(x_965);
x_1013 = l_Lean_identKind___closed__2;
lean_inc(x_1012);
x_1014 = l_Lean_Syntax_isOfKind(x_1012, x_1013);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_1012);
lean_dec(x_918);
lean_dec(x_223);
x_1015 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
lean_dec(x_1015);
x_1018 = l_Lean_Elab_Term_getEnv___rarg(x_1017);
x_1019 = lean_ctor_get(x_1018, 1);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 0);
lean_inc(x_1020);
lean_dec(x_1018);
x_1021 = lean_ctor_get(x_1019, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1019, 1);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1019, 2);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1019, 3);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1019, 4);
lean_inc(x_1025);
x_1026 = lean_ctor_get(x_1019, 5);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_3, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1027, 3);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 4);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_environment_main_module(x_1020);
x_1031 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1031, 0, x_1030);
lean_ctor_set(x_1031, 1, x_1016);
lean_ctor_set(x_1031, 2, x_1028);
lean_ctor_set(x_1031, 3, x_1029);
lean_inc(x_1);
x_1032 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1031, x_1026);
if (lean_obj_tag(x_1032) == 0)
{
uint8_t x_1033; 
x_1033 = !lean_is_exclusive(x_1019);
if (x_1033 == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1034 = lean_ctor_get(x_1019, 5);
lean_dec(x_1034);
x_1035 = lean_ctor_get(x_1019, 4);
lean_dec(x_1035);
x_1036 = lean_ctor_get(x_1019, 3);
lean_dec(x_1036);
x_1037 = lean_ctor_get(x_1019, 2);
lean_dec(x_1037);
x_1038 = lean_ctor_get(x_1019, 1);
lean_dec(x_1038);
x_1039 = lean_ctor_get(x_1019, 0);
lean_dec(x_1039);
x_1040 = lean_ctor_get(x_1032, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1032, 1);
lean_inc(x_1041);
lean_dec(x_1032);
lean_ctor_set(x_1019, 5, x_1041);
x_5 = x_1040;
x_6 = x_1019;
goto block_33;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_1019);
x_1042 = lean_ctor_get(x_1032, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1032, 1);
lean_inc(x_1043);
lean_dec(x_1032);
x_1044 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1044, 0, x_1021);
lean_ctor_set(x_1044, 1, x_1022);
lean_ctor_set(x_1044, 2, x_1023);
lean_ctor_set(x_1044, 3, x_1024);
lean_ctor_set(x_1044, 4, x_1025);
lean_ctor_set(x_1044, 5, x_1043);
x_5 = x_1042;
x_6 = x_1044;
goto block_33;
}
}
else
{
lean_object* x_1045; 
lean_dec(x_1025);
lean_dec(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_2);
lean_dec(x_1);
x_1045 = lean_ctor_get(x_1032, 0);
lean_inc(x_1045);
lean_dec(x_1032);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; uint8_t x_1051; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1045, 1);
lean_inc(x_1047);
lean_dec(x_1045);
x_1048 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1048, 0, x_1047);
x_1049 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1049, 0, x_1048);
x_1050 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1046, x_1049, x_3, x_1019);
lean_dec(x_1046);
x_1051 = !lean_is_exclusive(x_1050);
if (x_1051 == 0)
{
return x_1050;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1052 = lean_ctor_get(x_1050, 0);
x_1053 = lean_ctor_get(x_1050, 1);
lean_inc(x_1053);
lean_inc(x_1052);
lean_dec(x_1050);
x_1054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
return x_1054;
}
}
else
{
lean_object* x_1055; uint8_t x_1056; 
lean_dec(x_3);
x_1055 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1019);
x_1056 = !lean_is_exclusive(x_1055);
if (x_1056 == 0)
{
return x_1055;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1057 = lean_ctor_get(x_1055, 0);
x_1058 = lean_ctor_get(x_1055, 1);
lean_inc(x_1058);
lean_inc(x_1057);
lean_dec(x_1055);
x_1059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1059, 0, x_1057);
lean_ctor_set(x_1059, 1, x_1058);
return x_1059;
}
}
}
}
else
{
lean_object* x_1060; lean_object* x_1061; 
x_1060 = l_Lean_Syntax_getArg(x_918, x_224);
lean_dec(x_918);
x_1061 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_223, x_1012, x_1060, x_2, x_3, x_4);
return x_1061;
}
}
}
}
}
}
}
}
}
block_1301:
{
if (x_1084 == 0)
{
if (x_1083 == 0)
{
uint8_t x_1085; 
lean_dec(x_823);
x_1085 = 0;
x_824 = x_1085;
goto block_1082;
}
else
{
lean_object* x_1086; lean_object* x_1087; uint8_t x_1088; 
x_1086 = l_Lean_Syntax_getArgs(x_823);
lean_dec(x_823);
x_1087 = lean_array_get_size(x_1086);
lean_dec(x_1086);
x_1088 = lean_nat_dec_eq(x_1087, x_80);
lean_dec(x_1087);
x_824 = x_1088;
goto block_1082;
}
}
else
{
lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; uint8_t x_1296; 
lean_dec(x_823);
x_1089 = lean_unsigned_to_nat(5u);
x_1090 = l_Lean_Syntax_getArg(x_1, x_1089);
lean_inc(x_1090);
x_1296 = l_Lean_Syntax_isOfKind(x_1090, x_815);
if (x_1296 == 0)
{
uint8_t x_1297; 
x_1297 = 0;
x_1091 = x_1297;
goto block_1295;
}
else
{
lean_object* x_1298; lean_object* x_1299; uint8_t x_1300; 
x_1298 = l_Lean_Syntax_getArgs(x_1090);
x_1299 = lean_array_get_size(x_1298);
lean_dec(x_1298);
x_1300 = lean_nat_dec_eq(x_1299, x_80);
lean_dec(x_1299);
x_1091 = x_1300;
goto block_1295;
}
block_1295:
{
if (x_1091 == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
lean_dec(x_1090);
lean_dec(x_223);
x_1092 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
x_1095 = l_Lean_Elab_Term_getEnv___rarg(x_1094);
x_1096 = lean_ctor_get(x_1095, 1);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1095, 0);
lean_inc(x_1097);
lean_dec(x_1095);
x_1098 = lean_ctor_get(x_1096, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1096, 1);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1096, 2);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1096, 3);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1096, 4);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1096, 5);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_3, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1104, 3);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1104, 4);
lean_inc(x_1106);
lean_dec(x_1104);
x_1107 = lean_environment_main_module(x_1097);
x_1108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_1093);
lean_ctor_set(x_1108, 2, x_1105);
lean_ctor_set(x_1108, 3, x_1106);
lean_inc(x_1);
x_1109 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1108, x_1103);
if (lean_obj_tag(x_1109) == 0)
{
uint8_t x_1110; 
x_1110 = !lean_is_exclusive(x_1096);
if (x_1110 == 0)
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1111 = lean_ctor_get(x_1096, 5);
lean_dec(x_1111);
x_1112 = lean_ctor_get(x_1096, 4);
lean_dec(x_1112);
x_1113 = lean_ctor_get(x_1096, 3);
lean_dec(x_1113);
x_1114 = lean_ctor_get(x_1096, 2);
lean_dec(x_1114);
x_1115 = lean_ctor_get(x_1096, 1);
lean_dec(x_1115);
x_1116 = lean_ctor_get(x_1096, 0);
lean_dec(x_1116);
x_1117 = lean_ctor_get(x_1109, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1109, 1);
lean_inc(x_1118);
lean_dec(x_1109);
lean_ctor_set(x_1096, 5, x_1118);
x_5 = x_1117;
x_6 = x_1096;
goto block_33;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
lean_dec(x_1096);
x_1119 = lean_ctor_get(x_1109, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1109, 1);
lean_inc(x_1120);
lean_dec(x_1109);
x_1121 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1121, 0, x_1098);
lean_ctor_set(x_1121, 1, x_1099);
lean_ctor_set(x_1121, 2, x_1100);
lean_ctor_set(x_1121, 3, x_1101);
lean_ctor_set(x_1121, 4, x_1102);
lean_ctor_set(x_1121, 5, x_1120);
x_5 = x_1119;
x_6 = x_1121;
goto block_33;
}
}
else
{
lean_object* x_1122; 
lean_dec(x_1102);
lean_dec(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1098);
lean_dec(x_2);
lean_dec(x_1);
x_1122 = lean_ctor_get(x_1109, 0);
lean_inc(x_1122);
lean_dec(x_1109);
if (lean_obj_tag(x_1122) == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
lean_dec(x_1122);
x_1125 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1125, 0, x_1124);
x_1126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1126, 0, x_1125);
x_1127 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1123, x_1126, x_3, x_1096);
lean_dec(x_1123);
x_1128 = !lean_is_exclusive(x_1127);
if (x_1128 == 0)
{
return x_1127;
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1129 = lean_ctor_get(x_1127, 0);
x_1130 = lean_ctor_get(x_1127, 1);
lean_inc(x_1130);
lean_inc(x_1129);
lean_dec(x_1127);
x_1131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1131, 0, x_1129);
lean_ctor_set(x_1131, 1, x_1130);
return x_1131;
}
}
else
{
lean_object* x_1132; uint8_t x_1133; 
lean_dec(x_3);
x_1132 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1096);
x_1133 = !lean_is_exclusive(x_1132);
if (x_1133 == 0)
{
return x_1132;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1134 = lean_ctor_get(x_1132, 0);
x_1135 = lean_ctor_get(x_1132, 1);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_1132);
x_1136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
return x_1136;
}
}
}
}
else
{
lean_object* x_1137; uint8_t x_1138; lean_object* x_1288; uint8_t x_1289; 
x_1137 = l_Lean_Syntax_getArg(x_1090, x_128);
lean_dec(x_1090);
x_1288 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_1137);
x_1289 = l_Lean_Syntax_isOfKind(x_1137, x_1288);
if (x_1289 == 0)
{
uint8_t x_1290; 
x_1290 = 0;
x_1138 = x_1290;
goto block_1287;
}
else
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; uint8_t x_1294; 
x_1291 = l_Lean_Syntax_getArgs(x_1137);
x_1292 = lean_array_get_size(x_1291);
lean_dec(x_1291);
x_1293 = lean_unsigned_to_nat(3u);
x_1294 = lean_nat_dec_eq(x_1292, x_1293);
lean_dec(x_1292);
x_1138 = x_1294;
goto block_1287;
}
block_1287:
{
if (x_1138 == 0)
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
lean_dec(x_1137);
lean_dec(x_223);
x_1139 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1140 = lean_ctor_get(x_1139, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1139, 1);
lean_inc(x_1141);
lean_dec(x_1139);
x_1142 = l_Lean_Elab_Term_getEnv___rarg(x_1141);
x_1143 = lean_ctor_get(x_1142, 1);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1142, 0);
lean_inc(x_1144);
lean_dec(x_1142);
x_1145 = lean_ctor_get(x_1143, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1143, 1);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1143, 2);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1143, 3);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1143, 4);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1143, 5);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_3, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1151, 3);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1151, 4);
lean_inc(x_1153);
lean_dec(x_1151);
x_1154 = lean_environment_main_module(x_1144);
x_1155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_1140);
lean_ctor_set(x_1155, 2, x_1152);
lean_ctor_set(x_1155, 3, x_1153);
lean_inc(x_1);
x_1156 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1155, x_1150);
if (lean_obj_tag(x_1156) == 0)
{
uint8_t x_1157; 
x_1157 = !lean_is_exclusive(x_1143);
if (x_1157 == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1158 = lean_ctor_get(x_1143, 5);
lean_dec(x_1158);
x_1159 = lean_ctor_get(x_1143, 4);
lean_dec(x_1159);
x_1160 = lean_ctor_get(x_1143, 3);
lean_dec(x_1160);
x_1161 = lean_ctor_get(x_1143, 2);
lean_dec(x_1161);
x_1162 = lean_ctor_get(x_1143, 1);
lean_dec(x_1162);
x_1163 = lean_ctor_get(x_1143, 0);
lean_dec(x_1163);
x_1164 = lean_ctor_get(x_1156, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1156, 1);
lean_inc(x_1165);
lean_dec(x_1156);
lean_ctor_set(x_1143, 5, x_1165);
x_5 = x_1164;
x_6 = x_1143;
goto block_33;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1143);
x_1166 = lean_ctor_get(x_1156, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1156, 1);
lean_inc(x_1167);
lean_dec(x_1156);
x_1168 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1168, 0, x_1145);
lean_ctor_set(x_1168, 1, x_1146);
lean_ctor_set(x_1168, 2, x_1147);
lean_ctor_set(x_1168, 3, x_1148);
lean_ctor_set(x_1168, 4, x_1149);
lean_ctor_set(x_1168, 5, x_1167);
x_5 = x_1166;
x_6 = x_1168;
goto block_33;
}
}
else
{
lean_object* x_1169; 
lean_dec(x_1149);
lean_dec(x_1148);
lean_dec(x_1147);
lean_dec(x_1146);
lean_dec(x_1145);
lean_dec(x_2);
lean_dec(x_1);
x_1169 = lean_ctor_get(x_1156, 0);
lean_inc(x_1169);
lean_dec(x_1156);
if (lean_obj_tag(x_1169) == 0)
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; 
x_1170 = lean_ctor_get(x_1169, 0);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1169, 1);
lean_inc(x_1171);
lean_dec(x_1169);
x_1172 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1172, 0, x_1171);
x_1173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1173, 0, x_1172);
x_1174 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1170, x_1173, x_3, x_1143);
lean_dec(x_1170);
x_1175 = !lean_is_exclusive(x_1174);
if (x_1175 == 0)
{
return x_1174;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1174, 0);
x_1177 = lean_ctor_get(x_1174, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1174);
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
return x_1178;
}
}
else
{
lean_object* x_1179; uint8_t x_1180; 
lean_dec(x_3);
x_1179 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1143);
x_1180 = !lean_is_exclusive(x_1179);
if (x_1180 == 0)
{
return x_1179;
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1179, 0);
x_1182 = lean_ctor_get(x_1179, 1);
lean_inc(x_1182);
lean_inc(x_1181);
lean_dec(x_1179);
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set(x_1183, 1, x_1182);
return x_1183;
}
}
}
}
else
{
lean_object* x_1184; uint8_t x_1185; uint8_t x_1282; 
x_1184 = l_Lean_Syntax_getArg(x_1137, x_128);
lean_inc(x_1184);
x_1282 = l_Lean_Syntax_isOfKind(x_1184, x_815);
if (x_1282 == 0)
{
uint8_t x_1283; 
x_1283 = 0;
x_1185 = x_1283;
goto block_1281;
}
else
{
lean_object* x_1284; lean_object* x_1285; uint8_t x_1286; 
x_1284 = l_Lean_Syntax_getArgs(x_1184);
x_1285 = lean_array_get_size(x_1284);
lean_dec(x_1284);
x_1286 = lean_nat_dec_eq(x_1285, x_80);
lean_dec(x_1285);
x_1185 = x_1286;
goto block_1281;
}
block_1281:
{
if (x_1185 == 0)
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
lean_dec(x_1184);
lean_dec(x_1137);
lean_dec(x_223);
x_1186 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1187 = lean_ctor_get(x_1186, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1186, 1);
lean_inc(x_1188);
lean_dec(x_1186);
x_1189 = l_Lean_Elab_Term_getEnv___rarg(x_1188);
x_1190 = lean_ctor_get(x_1189, 1);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1189, 0);
lean_inc(x_1191);
lean_dec(x_1189);
x_1192 = lean_ctor_get(x_1190, 0);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1190, 1);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1190, 2);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1190, 3);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1190, 4);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1190, 5);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_3, 0);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1198, 3);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 4);
lean_inc(x_1200);
lean_dec(x_1198);
x_1201 = lean_environment_main_module(x_1191);
x_1202 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1202, 0, x_1201);
lean_ctor_set(x_1202, 1, x_1187);
lean_ctor_set(x_1202, 2, x_1199);
lean_ctor_set(x_1202, 3, x_1200);
lean_inc(x_1);
x_1203 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1202, x_1197);
if (lean_obj_tag(x_1203) == 0)
{
uint8_t x_1204; 
x_1204 = !lean_is_exclusive(x_1190);
if (x_1204 == 0)
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1205 = lean_ctor_get(x_1190, 5);
lean_dec(x_1205);
x_1206 = lean_ctor_get(x_1190, 4);
lean_dec(x_1206);
x_1207 = lean_ctor_get(x_1190, 3);
lean_dec(x_1207);
x_1208 = lean_ctor_get(x_1190, 2);
lean_dec(x_1208);
x_1209 = lean_ctor_get(x_1190, 1);
lean_dec(x_1209);
x_1210 = lean_ctor_get(x_1190, 0);
lean_dec(x_1210);
x_1211 = lean_ctor_get(x_1203, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1203, 1);
lean_inc(x_1212);
lean_dec(x_1203);
lean_ctor_set(x_1190, 5, x_1212);
x_5 = x_1211;
x_6 = x_1190;
goto block_33;
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
lean_dec(x_1190);
x_1213 = lean_ctor_get(x_1203, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1203, 1);
lean_inc(x_1214);
lean_dec(x_1203);
x_1215 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1215, 0, x_1192);
lean_ctor_set(x_1215, 1, x_1193);
lean_ctor_set(x_1215, 2, x_1194);
lean_ctor_set(x_1215, 3, x_1195);
lean_ctor_set(x_1215, 4, x_1196);
lean_ctor_set(x_1215, 5, x_1214);
x_5 = x_1213;
x_6 = x_1215;
goto block_33;
}
}
else
{
lean_object* x_1216; 
lean_dec(x_1196);
lean_dec(x_1195);
lean_dec(x_1194);
lean_dec(x_1193);
lean_dec(x_1192);
lean_dec(x_2);
lean_dec(x_1);
x_1216 = lean_ctor_get(x_1203, 0);
lean_inc(x_1216);
lean_dec(x_1203);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; 
x_1217 = lean_ctor_get(x_1216, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1216, 1);
lean_inc(x_1218);
lean_dec(x_1216);
x_1219 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1219, 0, x_1218);
x_1220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1220, 0, x_1219);
x_1221 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1217, x_1220, x_3, x_1190);
lean_dec(x_1217);
x_1222 = !lean_is_exclusive(x_1221);
if (x_1222 == 0)
{
return x_1221;
}
else
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
x_1223 = lean_ctor_get(x_1221, 0);
x_1224 = lean_ctor_get(x_1221, 1);
lean_inc(x_1224);
lean_inc(x_1223);
lean_dec(x_1221);
x_1225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1225, 0, x_1223);
lean_ctor_set(x_1225, 1, x_1224);
return x_1225;
}
}
else
{
lean_object* x_1226; uint8_t x_1227; 
lean_dec(x_3);
x_1226 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1190);
x_1227 = !lean_is_exclusive(x_1226);
if (x_1227 == 0)
{
return x_1226;
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1228 = lean_ctor_get(x_1226, 0);
x_1229 = lean_ctor_get(x_1226, 1);
lean_inc(x_1229);
lean_inc(x_1228);
lean_dec(x_1226);
x_1230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1230, 0, x_1228);
lean_ctor_set(x_1230, 1, x_1229);
return x_1230;
}
}
}
}
else
{
lean_object* x_1231; lean_object* x_1232; uint8_t x_1233; 
x_1231 = l_Lean_Syntax_getArg(x_1184, x_128);
lean_dec(x_1184);
x_1232 = l_Lean_identKind___closed__2;
lean_inc(x_1231);
x_1233 = l_Lean_Syntax_isOfKind(x_1231, x_1232);
if (x_1233 == 0)
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1231);
lean_dec(x_1137);
lean_dec(x_223);
x_1234 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1235 = lean_ctor_get(x_1234, 0);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1234, 1);
lean_inc(x_1236);
lean_dec(x_1234);
x_1237 = l_Lean_Elab_Term_getEnv___rarg(x_1236);
x_1238 = lean_ctor_get(x_1237, 1);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1237, 0);
lean_inc(x_1239);
lean_dec(x_1237);
x_1240 = lean_ctor_get(x_1238, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1238, 1);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1238, 2);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1238, 3);
lean_inc(x_1243);
x_1244 = lean_ctor_get(x_1238, 4);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1238, 5);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_3, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1246, 3);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_1246, 4);
lean_inc(x_1248);
lean_dec(x_1246);
x_1249 = lean_environment_main_module(x_1239);
x_1250 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1235);
lean_ctor_set(x_1250, 2, x_1247);
lean_ctor_set(x_1250, 3, x_1248);
lean_inc(x_1);
x_1251 = l___private_Lean_Elab_Match_41__expandMatchDiscr_x3f(x_1, x_1250, x_1245);
if (lean_obj_tag(x_1251) == 0)
{
uint8_t x_1252; 
x_1252 = !lean_is_exclusive(x_1238);
if (x_1252 == 0)
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1253 = lean_ctor_get(x_1238, 5);
lean_dec(x_1253);
x_1254 = lean_ctor_get(x_1238, 4);
lean_dec(x_1254);
x_1255 = lean_ctor_get(x_1238, 3);
lean_dec(x_1255);
x_1256 = lean_ctor_get(x_1238, 2);
lean_dec(x_1256);
x_1257 = lean_ctor_get(x_1238, 1);
lean_dec(x_1257);
x_1258 = lean_ctor_get(x_1238, 0);
lean_dec(x_1258);
x_1259 = lean_ctor_get(x_1251, 0);
lean_inc(x_1259);
x_1260 = lean_ctor_get(x_1251, 1);
lean_inc(x_1260);
lean_dec(x_1251);
lean_ctor_set(x_1238, 5, x_1260);
x_5 = x_1259;
x_6 = x_1238;
goto block_33;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
lean_dec(x_1238);
x_1261 = lean_ctor_get(x_1251, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1251, 1);
lean_inc(x_1262);
lean_dec(x_1251);
x_1263 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1263, 0, x_1240);
lean_ctor_set(x_1263, 1, x_1241);
lean_ctor_set(x_1263, 2, x_1242);
lean_ctor_set(x_1263, 3, x_1243);
lean_ctor_set(x_1263, 4, x_1244);
lean_ctor_set(x_1263, 5, x_1262);
x_5 = x_1261;
x_6 = x_1263;
goto block_33;
}
}
else
{
lean_object* x_1264; 
lean_dec(x_1244);
lean_dec(x_1243);
lean_dec(x_1242);
lean_dec(x_1241);
lean_dec(x_1240);
lean_dec(x_2);
lean_dec(x_1);
x_1264 = lean_ctor_get(x_1251, 0);
lean_inc(x_1264);
lean_dec(x_1251);
if (lean_obj_tag(x_1264) == 0)
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; uint8_t x_1270; 
x_1265 = lean_ctor_get(x_1264, 0);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1264, 1);
lean_inc(x_1266);
lean_dec(x_1264);
x_1267 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1267, 0, x_1266);
x_1268 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1268, 0, x_1267);
x_1269 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1265, x_1268, x_3, x_1238);
lean_dec(x_1265);
x_1270 = !lean_is_exclusive(x_1269);
if (x_1270 == 0)
{
return x_1269;
}
else
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1271 = lean_ctor_get(x_1269, 0);
x_1272 = lean_ctor_get(x_1269, 1);
lean_inc(x_1272);
lean_inc(x_1271);
lean_dec(x_1269);
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1271);
lean_ctor_set(x_1273, 1, x_1272);
return x_1273;
}
}
else
{
lean_object* x_1274; uint8_t x_1275; 
lean_dec(x_3);
x_1274 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1238);
x_1275 = !lean_is_exclusive(x_1274);
if (x_1275 == 0)
{
return x_1274;
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1276 = lean_ctor_get(x_1274, 0);
x_1277 = lean_ctor_get(x_1274, 1);
lean_inc(x_1277);
lean_inc(x_1276);
lean_dec(x_1274);
x_1278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1278, 0, x_1276);
lean_ctor_set(x_1278, 1, x_1277);
return x_1278;
}
}
}
}
else
{
lean_object* x_1279; lean_object* x_1280; 
x_1279 = l_Lean_Syntax_getArg(x_1137, x_224);
lean_dec(x_1137);
x_1280 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_223, x_1231, x_1279, x_2, x_3, x_4);
return x_1280;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_match___elambda__1___closed__2;
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
lean_object* l_Lean_Elab_Term_elabNoMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Term_nomatch___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_Match_33__waitExpectedType(x_2, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkOptionalNode___closed__2;
x_19 = lean_array_push(x_18, x_14);
x_20 = l_Array_empty___closed__1;
x_21 = l_Lean_mkOptionalNode___closed__1;
x_22 = l___private_Lean_Elab_Match_32__elabMatchAux(x_19, x_20, x_21, x_16, x_3, x_17);
lean_dec(x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNoMatch), 4, 0);
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
lean_object* initialize_Lean_Meta_EqnCompiler_MatchPatternAttr(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_Match(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6);
l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1 = _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1);
l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2 = _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2);
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
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14);
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
res = l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1 = _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1);
l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2 = _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2);
l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3 = _init_l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3);
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
l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1 = _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1);
l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2 = _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2);
l___private_Lean_Elab_Match_16__processIdAux___closed__1 = _init_l___private_Lean_Elab_Match_16__processIdAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___closed__1);
l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2);
l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3 = _init_l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__4 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__4);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12);
l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13 = _init_l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2);
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3);
l___private_Lean_Elab_Match_21__collectPatternVars___closed__1 = _init_l___private_Lean_Elab_Match_21__collectPatternVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_21__collectPatternVars___closed__1);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__1);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__4);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__5);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__6);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__7 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__7();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__7);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__8 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__8();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__8);
l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__9 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__9();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1___closed__9);
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
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__6);
l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7 = _init_l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkMatchType___main___closed__7);
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
l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__6 = _init_l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_37__mkNewDiscrs___main___closed__6);
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
l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNoMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
