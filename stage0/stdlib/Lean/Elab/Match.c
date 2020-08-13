// Lean compiler output
// Module: Lean.Elab.Match
// Imports: Init Lean.Meta.EqnCompiler.MatchPattern Lean.Meta.EqnCompiler.DepElim Lean.Elab.SyntheticMVars
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
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__2;
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___closed__4;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2;
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__12;
lean_object* l_Lean_Syntax_getIdOfTermId(lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__4;
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_37__mkNewAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__1;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1;
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__1;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFromIdent(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_37__mkNewAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__8;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_8__getMatchAlts___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__2;
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6;
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__1;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_16__processIdAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__10;
extern lean_object* l_Lean_Parser_Term_eq___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__9;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__2;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
lean_object* l_Lean_Elab_Term_elabMVarWithIdKind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_23__withPatternVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_33__mkOptType(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_30__elabPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main(uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_37__mkNewAlts(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_18__processNonVariable___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabInaccessible(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___closed__1;
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10;
lean_object* l___private_Lean_Elab_Match_15__processVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__1;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__3(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__7;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__9;
lean_object* l___private_Lean_Elab_Match_29__getFieldsBinderInfo___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern(lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_finalizePatternDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__4;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__7;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__8;
lean_object* l_Lean_Elab_Term_finalizePatternDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___main___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_toDepElimPattern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_10__mkMVarSyntax(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_21__collectPatternVars___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_30__elabPatterns___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
lean_object* l___private_Lean_Elab_Match_39__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_Match_30__elabPatterns___closed__1;
extern lean_object* l_Lean_Nat_HasQuote___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
lean_object* l_Lean_Elab_Term_CollectPatternVars_withRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__withAltsAux___main___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__2;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__2;
lean_object* l___private_Lean_Elab_Match_26__markAsVisited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2(uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern(lean_object*);
extern lean_object* l_Lean_EqnCompiler_matchPatternAttr;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___closed__1;
lean_object* l___private_Lean_Elab_Match_26__markAsVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_16__processIdAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_String_HasQuote___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous(lean_object*);
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_30__elabPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind(lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__3;
lean_object* l_Lean_Elab_Term_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__2;
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_inaccessible_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_29__getFieldsBinderInfo(lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__2;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
lean_object* l_Lean_Elab_expandMacros___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_37__mkNewAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg___closed__1;
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_25__alreadyVisited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
extern lean_object* l_Lean_Options_empty;
lean_object* l___private_Lean_Elab_Match_30__elabPatterns___closed__3;
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabDiscrsAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
lean_object* l_StateT_bind___at___private_Lean_Elab_Match_16__processIdAux___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Match_8__getMatchAlts___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabInaccessible(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__3;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___closed__6;
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___closed__2;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
lean_object* l_Lean_Elab_Term_inaccessible_x3f(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg___closed__3;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__1;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString___closed__1;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___closed__1;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_MessageData_ofArray(lean_object*);
lean_object* l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(lean_object*);
extern lean_object* l_Lean_Meta_mkEqRefl___closed__2;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInaccessible___closed__1;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_withRef(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__mkMatchType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__7;
extern lean_object* l_Lean_Parser_Command_openRenamingItem___elambda__1___closed__5;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__2;
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
lean_object* l_List_map___main___at_Lean_MessageData_coeOfListExpr___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
lean_object* l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift___at___private_Lean_Elab_Match_16__processIdAux___spec__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_finalizePatternDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMotiveType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3;
extern lean_object* l_Lean_Parser_Term_inaccessible___elambda__1___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_36__mkNewAlt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__3;
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux(lean_object*);
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__6;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
lean_object* l_Lean_Elab_Term_mkMotiveType___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabInaccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_18__processId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isTermId_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Match_23__withPatternVars(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3___closed__3;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_setOptionFromString___closed__1;
lean_object* l___private_Lean_Elab_Match_20__collect___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__1;
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___closed__3;
lean_object* l___private_Lean_Elab_Match_12__throwCtorExpected___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__2;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l___private_Lean_Elab_Match_9__registerAuxiliaryNodeKind___closed__1;
lean_object* l___private_Lean_Elab_Match_36__mkNewAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Closure_mkNextUserName___rarg___closed__2;
lean_object* l___private_Lean_Elab_Match_24__elabPatternsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_37__mkNewAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkMotiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__1;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__11;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__11;
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__10;
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_37__mkNewAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__6;
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5;
lean_object* l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__3;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__5;
extern lean_object* l_Nat_Inhabited;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_PatternVar_hasToString(lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Match_13__getNumExplicitCtorParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13;
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__5;
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Elab_Term_elabMatchAltView___spec__2(uint8_t, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_22__withPatternVarsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___closed__2;
lean_object* l___private_Lean_Elab_Match_22__withPatternVarsAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__3;
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_7__elabDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2;
lean_object* l___private_Lean_Elab_Match_15__processVar___closed__5;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMVarWithIdKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_17__processCtor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__3;
extern lean_object* l_Lean_Parser_Term_char___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_28__getFieldsBinderInfoAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
lean_object* l___private_Lean_Elab_Match_5__elabMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l_Lean_mkThunk(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabDiscrsAux___main___closed__6;
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
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
x_14 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_15 = lean_array_push(x_13, x_14);
x_16 = lean_array_push(x_15, x_14);
x_17 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_18 = lean_array_push(x_16, x_17);
x_19 = lean_array_push(x_18, x_2);
x_20 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_array_push(x_25, x_4);
x_27 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_6, 7);
lean_inc(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_6, 7, x_32);
x_33 = 1;
x_34 = l_Lean_Elab_Term_elabTerm(x_28, x_5, x_33, x_6, x_11);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_ctor_get(x_6, 3);
x_39 = lean_ctor_get(x_6, 4);
x_40 = lean_ctor_get(x_6, 5);
x_41 = lean_ctor_get(x_6, 6);
x_42 = lean_ctor_get(x_6, 7);
x_43 = lean_ctor_get(x_6, 8);
x_44 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_45 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_47 = lean_ctor_get(x_6, 9);
lean_inc(x_47);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
lean_inc(x_28);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
x_50 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_37);
lean_ctor_set(x_50, 3, x_38);
lean_ctor_set(x_50, 4, x_39);
lean_ctor_set(x_50, 5, x_40);
lean_ctor_set(x_50, 6, x_41);
lean_ctor_set(x_50, 7, x_49);
lean_ctor_set(x_50, 8, x_43);
lean_ctor_set(x_50, 9, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*10, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 1, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 2, x_46);
x_51 = 1;
x_52 = l_Lean_Elab_Term_elabTerm(x_28, x_5, x_51, x_50, x_11);
return x_52;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
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
x_15 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
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
x_28 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_32 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_array_push(x_33, x_5);
x_35 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_7, 7);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_7, 7, x_40);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTerm(x_36, x_6, x_41, x_7, x_12);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
x_45 = lean_ctor_get(x_7, 2);
x_46 = lean_ctor_get(x_7, 3);
x_47 = lean_ctor_get(x_7, 4);
x_48 = lean_ctor_get(x_7, 5);
x_49 = lean_ctor_get(x_7, 6);
x_50 = lean_ctor_get(x_7, 7);
x_51 = lean_ctor_get(x_7, 8);
x_52 = lean_ctor_get_uint8(x_7, sizeof(void*)*10);
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 1);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 2);
x_55 = lean_ctor_get(x_7, 9);
lean_inc(x_55);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
lean_inc(x_36);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_36);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
x_58 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_44);
lean_ctor_set(x_58, 2, x_45);
lean_ctor_set(x_58, 3, x_46);
lean_ctor_set(x_58, 4, x_47);
lean_ctor_set(x_58, 5, x_48);
lean_ctor_set(x_58, 6, x_49);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_51);
lean_ctor_set(x_58, 9, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 2, x_54);
x_59 = 1;
x_60 = l_Lean_Elab_Term_elabTerm(x_36, x_6, x_59, x_58, x_12);
return x_60;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 5);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 4);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_environment_main_module(x_12);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_1, x_6, x_2, x_19, x_14);
lean_dec(x_19);
lean_dec(x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_11, 5, x_22);
x_23 = l_Lean_Elab_Term_elabType(x_21, x_3, x_11);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 4);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_environment_main_module(x_12);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
x_35 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_1, x_6, x_2, x_34, x_29);
lean_dec(x_34);
lean_dec(x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
lean_ctor_set(x_38, 3, x_27);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_37);
x_39 = l_Lean_Elab_Term_elabType(x_36, x_3, x_38);
return x_39;
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 2);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = 1;
lean_inc(x_6);
lean_inc(x_57);
x_59 = l_Lean_Elab_Term_elabTerm(x_38, x_57, x_58, x_6, x_41);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_6);
x_62 = l_Lean_Elab_Term_ensureHasType(x_57, x_60, x_6, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_3, x_65);
lean_dec(x_3);
x_67 = lean_expr_instantiate1(x_56, x_63);
lean_dec(x_56);
x_68 = lean_array_push(x_5, x_63);
x_3 = x_66;
x_4 = x_67;
x_5 = x_68;
x_7 = x_64;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
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
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_78; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_box(0);
x_42 = x_78;
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
uint8_t x_79; 
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_39);
if (x_79 == 0)
{
return x_39;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_39, 0);
x_81 = lean_ctor_get(x_39, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_39);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
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
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = l_Lean_Name_eraseMacroScopes(x_1);
x_7 = l_Lean_Name_isAtomic(x_6);
lean_dec(x_6);
if (x_2 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_8 = x_56;
goto block_55;
}
else
{
uint8_t x_57; 
x_57 = 1;
x_8 = x_57;
goto block_55;
}
block_55:
{
uint8_t x_9; 
if (x_7 == 0)
{
uint8_t x_53; 
x_53 = 0;
x_9 = x_53;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = 1;
x_9 = x_54;
goto block_52;
}
block_52:
{
lean_object* x_10; lean_object* x_11; 
if (x_8 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
x_10 = x_46;
x_11 = x_5;
goto block_44;
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_1);
x_47 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_3, x_4, x_5);
lean_dec(x_3);
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
block_44:
{
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_1);
x_12 = l___private_Lean_Elab_Match_15__processVar___closed__3;
x_13 = l_Lean_Elab_Term_throwError___rarg(x_12, x_4, x_11);
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
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_19 = x_10;
} else {
 lean_dec_ref(x_10);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = l_Lean_NameSet_contains(x_20, x_1);
if (x_21 == 0)
{
uint8_t x_42; 
x_42 = 0;
x_22 = x_42;
goto block_41;
}
else
{
uint8_t x_43; 
x_43 = 1;
x_22 = x_43;
goto block_41;
}
block_41:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_23 = lean_box(0);
lean_inc(x_1);
x_24 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_20, x_1, x_23);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = lean_array_push(x_25, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_19)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_19;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = l___private_Lean_Elab_Match_15__processVar___closed__6;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Match_15__processVar___closed__9;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Term_throwError___rarg(x_35, x_4, x_11);
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
lean_object* x_1; 
x_1 = lean_mk_string("invalid occurrence of named pattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_16__processIdAux___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_Syntax_isTermId_x3f(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_5, x_6, x_7);
lean_dec(x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_13, x_15);
lean_dec(x_13);
x_17 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_115; 
x_115 = 0;
x_19 = x_115;
goto block_114;
}
else
{
x_19 = x_8;
goto block_114;
}
block_114:
{
lean_object* x_20; lean_object* x_21; lean_object* x_79; lean_object* x_80; 
if (x_19 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_5);
x_79 = x_107;
x_80 = x_7;
goto block_105;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__3;
x_109 = l_Lean_Elab_Term_throwError___rarg(x_108, x_6, x_7);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
block_78:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_45 = lean_box(0);
x_46 = l_List_filterAux___main___at___private_Lean_Elab_Match_16__processIdAux___spec__2(x_22, x_45);
x_47 = l_List_map___main___at___private_Lean_Elab_Match_16__processIdAux___spec__3(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_4);
x_48 = lean_box(0);
x_25 = x_48;
goto block_44;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
if (lean_obj_tag(x_50) == 4)
{
lean_object* x_51; lean_object* x_52; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_51);
lean_inc(x_4);
x_59 = lean_environment_find(x_4, x_51);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_51);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_60 = l___private_Lean_Elab_Match_12__throwCtorExpected___rarg(x_23, x_6, x_21);
lean_dec(x_23);
return x_60;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 6)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_4);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Elab_Match_13__getNumExplicitCtorParams(x_62, x_6, x_21);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
if (lean_is_scalar(x_14)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_14;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
if (lean_is_scalar(x_14)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_14;
}
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_23);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_23);
lean_dec(x_14);
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
return x_63;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_14);
x_75 = lean_box(0);
x_52 = x_75;
goto block_58;
}
}
block_58:
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_52);
x_53 = l_Lean_EqnCompiler_matchPatternAttr;
x_54 = l_Lean_TagAttribute_hasTag(x_53, x_4, x_51);
lean_dec(x_51);
lean_dec(x_4);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_24);
x_55 = lean_box(0);
x_25 = x_55;
goto block_44;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_12);
lean_dec(x_6);
if (lean_is_scalar(x_24)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_24;
}
lean_ctor_set(x_56, 0, x_15);
lean_ctor_set(x_56, 1, x_23);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_21);
return x_57;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_50);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_4);
x_76 = lean_box(0);
x_25 = x_76;
goto block_44;
}
}
else
{
lean_object* x_77; 
lean_dec(x_49);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_77 = l___private_Lean_Elab_Match_14__throwAmbiguous___rarg(x_47, x_23, x_6, x_21);
lean_dec(x_23);
return x_77;
}
}
block_44:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_25);
x_26 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_27 = l___private_Lean_Elab_Match_15__processVar(x_26, x_2, x_23, x_6, x_21);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_15);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
block_105:
{
if (lean_obj_tag(x_12) == 3)
{
uint8_t x_81; 
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
x_83 = lean_ctor_get(x_12, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_12, 3);
lean_inc(x_84);
x_85 = lean_box(0);
lean_inc(x_6);
x_86 = l_Lean_Elab_Term_resolveName(x_83, x_84, x_85, x_6, x_80);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_ctor_set(x_79, 0, x_87);
x_20 = x_79;
x_21 = x_88;
goto block_78;
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_ctor_set(x_79, 0, x_85);
x_20 = x_79;
x_21 = x_89;
goto block_78;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_dec(x_79);
x_91 = lean_ctor_get(x_12, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_12, 3);
lean_inc(x_92);
x_93 = lean_box(0);
lean_inc(x_6);
x_94 = l_Lean_Elab_Term_resolveName(x_91, x_92, x_93, x_6, x_80);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_90);
x_20 = x_97;
x_21 = x_96;
goto block_78;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_90);
x_20 = x_99;
x_21 = x_98;
goto block_78;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_100 = lean_ctor_get(x_79, 1);
lean_inc(x_100);
lean_dec(x_79);
x_101 = l_Nat_Inhabited;
x_102 = l_monadInhabited___rarg(x_3, x_101);
x_103 = l_unreachable_x21___rarg(x_102);
x_104 = lean_apply_3(x_103, x_100, x_6, x_80);
return x_104;
}
}
}
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
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_6);
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
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_Match_16__processIdAux___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
lean_inc(x_1);
x_16 = lean_name_mk_string(x_1, x_15);
lean_inc(x_12);
x_17 = l_Lean_Syntax_isOfKind(x_12, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_12);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_4);
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
x_5 = lean_unsigned_to_nat(2u);
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
x_25 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
lean_inc(x_2);
x_26 = lean_name_mk_string(x_2, x_25);
x_27 = lean_name_eq(x_3, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_mkTermIdFromIdent___closed__1;
lean_inc(x_2);
x_29 = lean_name_mk_string(x_2, x_28);
x_30 = lean_name_eq(x_3, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_31 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
lean_inc(x_2);
x_32 = lean_name_mk_string(x_2, x_31);
x_33 = lean_name_eq(x_3, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_String_HasQuote___closed__1;
lean_inc(x_2);
x_35 = lean_name_mk_string(x_2, x_34);
x_36 = lean_name_eq(x_3, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Nat_HasQuote___closed__1;
lean_inc(x_2);
x_38 = lean_name_mk_string(x_2, x_37);
x_39 = lean_name_eq(x_3, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = l_Lean_Parser_Term_char___elambda__1___closed__1;
x_41 = lean_name_mk_string(x_2, x_40);
x_42 = lean_name_eq(x_3, x_41);
lean_dec(x_41);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_3);
x_60 = l_Lean_Syntax_inhabited;
x_61 = lean_array_get(x_60, x_5, x_12);
lean_dec(x_5);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Syntax_getArg(x_61, x_63);
lean_dec(x_61);
x_65 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_inc(x_2);
x_66 = lean_name_mk_string(x_2, x_65);
lean_inc(x_64);
x_67 = l_Lean_Syntax_isOfKind(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_69 = lean_name_mk_string(x_2, x_68);
lean_inc(x_64);
x_70 = l_Lean_Syntax_isOfKind(x_64, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_64);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_4);
x_71 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_8, x_9);
lean_dec(x_7);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_72 = l_Lean_Syntax_getIdOfTermId(x_4);
x_73 = l_Lean_Syntax_getArg(x_64, x_12);
lean_dec(x_64);
x_74 = 0;
lean_inc(x_8);
lean_inc(x_72);
x_75 = l___private_Lean_Elab_Match_15__processVar(x_72, x_74, x_7, x_8, x_9);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_8);
x_79 = l___private_Lean_Elab_Match_20__collect___main(x_73, x_78, x_8, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_81);
lean_dec(x_8);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Term_getMainModule___rarg(x_86);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_91 = l_Lean_addMacroScope(x_89, x_90, x_85);
x_92 = l_Lean_SourceInfo_inhabited___closed__1;
x_93 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_94 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_94);
x_96 = l_Array_empty___closed__1;
x_97 = lean_array_push(x_96, x_95);
x_98 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_29);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_array_push(x_96, x_100);
x_102 = l_Lean_mkTermIdFrom(x_4, x_72);
lean_dec(x_4);
x_103 = lean_array_push(x_96, x_102);
x_104 = lean_array_push(x_103, x_83);
x_105 = l_Lean_nullKind___closed__2;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_array_push(x_101, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_80, 0, x_108);
lean_ctor_set(x_87, 0, x_80);
return x_87;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_109 = lean_ctor_get(x_87, 0);
x_110 = lean_ctor_get(x_87, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_87);
x_111 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_112 = l_Lean_addMacroScope(x_109, x_111, x_85);
x_113 = l_Lean_SourceInfo_inhabited___closed__1;
x_114 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_115 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set(x_116, 3, x_115);
x_117 = l_Array_empty___closed__1;
x_118 = lean_array_push(x_117, x_116);
x_119 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_120 = lean_array_push(x_118, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_29);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_push(x_117, x_121);
x_123 = l_Lean_mkTermIdFrom(x_4, x_72);
lean_dec(x_4);
x_124 = lean_array_push(x_117, x_123);
x_125 = lean_array_push(x_124, x_83);
x_126 = l_Lean_nullKind___closed__2;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_array_push(x_122, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_6);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_80, 0, x_129);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_80);
lean_ctor_set(x_130, 1, x_110);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_131 = lean_ctor_get(x_80, 0);
x_132 = lean_ctor_get(x_80, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_80);
x_133 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_81);
lean_dec(x_8);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Elab_Term_getMainModule___rarg(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_141 = l_Lean_addMacroScope(x_137, x_140, x_134);
x_142 = l_Lean_SourceInfo_inhabited___closed__1;
x_143 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_144 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_145 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_145, 2, x_141);
lean_ctor_set(x_145, 3, x_144);
x_146 = l_Array_empty___closed__1;
x_147 = lean_array_push(x_146, x_145);
x_148 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_149 = lean_array_push(x_147, x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_29);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_array_push(x_146, x_150);
x_152 = l_Lean_mkTermIdFrom(x_4, x_72);
lean_dec(x_4);
x_153 = lean_array_push(x_146, x_152);
x_154 = lean_array_push(x_153, x_131);
x_155 = l_Lean_nullKind___closed__2;
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_array_push(x_151, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_6);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_132);
if (lean_is_scalar(x_139)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_139;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_138);
return x_160;
}
}
else
{
uint8_t x_161; 
lean_dec(x_72);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_161 = !lean_is_exclusive(x_79);
if (x_161 == 0)
{
return x_79;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_79, 0);
x_163 = lean_ctor_get(x_79, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_79);
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
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_165 = !lean_is_exclusive(x_75);
if (x_165 == 0)
{
return x_75;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_75, 0);
x_167 = lean_ctor_get(x_75, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_75);
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
uint8_t x_169; lean_object* x_170; 
lean_dec(x_64);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_2);
x_169 = 1;
lean_inc(x_4);
x_170 = l___private_Lean_Elab_Match_16__processIdAux(x_4, x_169, x_7, x_8, x_9);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_172, 0);
lean_dec(x_174);
lean_ctor_set(x_172, 0, x_4);
return x_170;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_4);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_170, 0, x_176);
return x_170;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_170, 0);
x_178 = lean_ctor_get(x_170, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_170);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_4);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_178);
return x_182;
}
}
else
{
uint8_t x_183; 
lean_dec(x_4);
x_183 = !lean_is_exclusive(x_170);
if (x_183 == 0)
{
return x_170;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_170, 0);
x_185 = lean_ctor_get(x_170, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_170);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
else
{
lean_object* x_187; 
lean_dec(x_61);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_2);
lean_inc(x_4);
x_187 = l___private_Lean_Elab_Match_18__processId(x_4, x_7, x_8, x_9);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_189, 0);
lean_dec(x_191);
lean_ctor_set(x_189, 0, x_4);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_4);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_187, 0, x_193);
return x_187;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_187, 0);
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_187);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_4);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
return x_199;
}
}
else
{
uint8_t x_200; 
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_187);
if (x_200 == 0)
{
return x_187;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_187, 0);
x_202 = lean_ctor_get(x_187, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_187);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
lean_dec(x_6);
x_204 = l_Lean_Syntax_inhabited;
x_205 = lean_array_get(x_204, x_5, x_12);
x_206 = l_Lean_Syntax_isNone(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_4);
x_207 = lean_unsigned_to_nat(0u);
x_208 = l_Lean_Syntax_getArg(x_205, x_207);
x_209 = l_Lean_Syntax_getArg(x_205, x_12);
x_210 = l_Lean_Syntax_isNone(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = l_Lean_Syntax_getArg(x_209, x_207);
x_212 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_213 = lean_name_mk_string(x_2, x_212);
lean_inc(x_211);
x_214 = l_Lean_Syntax_isOfKind(x_211, x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; 
lean_inc(x_8);
x_215 = l___private_Lean_Elab_Match_20__collect___main(x_208, x_7, x_8, x_9);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = l_Lean_Syntax_setArg(x_205, x_207, x_218);
x_221 = l_Lean_Syntax_getArg(x_211, x_12);
x_222 = l_Lean_Syntax_getArgs(x_221);
lean_dec(x_221);
x_223 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_224 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_222, x_223, x_219, x_8, x_217);
lean_dec(x_222);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_224, 0);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = l_Lean_nullKind;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Lean_Syntax_setArg(x_211, x_12, x_230);
x_232 = l_Lean_Syntax_setArg(x_209, x_207, x_231);
x_233 = l_Lean_Syntax_setArg(x_220, x_12, x_232);
x_234 = lean_array_set(x_5, x_12, x_233);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_3);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_226, 0, x_235);
return x_224;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_236 = lean_ctor_get(x_226, 0);
x_237 = lean_ctor_get(x_226, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_226);
x_238 = l_Lean_nullKind;
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
x_240 = l_Lean_Syntax_setArg(x_211, x_12, x_239);
x_241 = l_Lean_Syntax_setArg(x_209, x_207, x_240);
x_242 = l_Lean_Syntax_setArg(x_220, x_12, x_241);
x_243 = lean_array_set(x_5, x_12, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_3);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_237);
lean_ctor_set(x_224, 0, x_245);
return x_224;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_246 = lean_ctor_get(x_224, 0);
x_247 = lean_ctor_get(x_224, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_224);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_250 = x_246;
} else {
 lean_dec_ref(x_246);
 x_250 = lean_box(0);
}
x_251 = l_Lean_nullKind;
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
x_253 = l_Lean_Syntax_setArg(x_211, x_12, x_252);
x_254 = l_Lean_Syntax_setArg(x_209, x_207, x_253);
x_255 = l_Lean_Syntax_setArg(x_220, x_12, x_254);
x_256 = lean_array_set(x_5, x_12, x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_3);
lean_ctor_set(x_257, 1, x_256);
if (lean_is_scalar(x_250)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_250;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_249);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_247);
return x_259;
}
}
else
{
uint8_t x_260; 
lean_dec(x_220);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_5);
lean_dec(x_3);
x_260 = !lean_is_exclusive(x_224);
if (x_260 == 0)
{
return x_224;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_224, 0);
x_262 = lean_ctor_get(x_224, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_224);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_264 = !lean_is_exclusive(x_215);
if (x_264 == 0)
{
return x_215;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_215, 0);
x_266 = lean_ctor_get(x_215, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_215);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
lean_object* x_268; 
lean_dec(x_211);
lean_dec(x_209);
x_268 = l___private_Lean_Elab_Match_20__collect___main(x_208, x_7, x_8, x_9);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; uint8_t x_271; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = l_Lean_Syntax_setArg(x_205, x_207, x_272);
x_274 = lean_array_set(x_5, x_12, x_273);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_3);
lean_ctor_set(x_275, 1, x_274);
lean_ctor_set(x_270, 0, x_275);
return x_268;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_276 = lean_ctor_get(x_270, 0);
x_277 = lean_ctor_get(x_270, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_270);
x_278 = l_Lean_Syntax_setArg(x_205, x_207, x_276);
x_279 = lean_array_set(x_5, x_12, x_278);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_3);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_277);
lean_ctor_set(x_268, 0, x_281);
return x_268;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_282 = lean_ctor_get(x_268, 0);
x_283 = lean_ctor_get(x_268, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_268);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_286 = x_282;
} else {
 lean_dec_ref(x_282);
 x_286 = lean_box(0);
}
x_287 = l_Lean_Syntax_setArg(x_205, x_207, x_284);
x_288 = lean_array_set(x_5, x_12, x_287);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_3);
lean_ctor_set(x_289, 1, x_288);
if (lean_is_scalar(x_286)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_286;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_285);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_283);
return x_291;
}
}
else
{
uint8_t x_292; 
lean_dec(x_205);
lean_dec(x_5);
lean_dec(x_3);
x_292 = !lean_is_exclusive(x_268);
if (x_292 == 0)
{
return x_268;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_268, 0);
x_294 = lean_ctor_get(x_268, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_268);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
else
{
lean_object* x_296; 
lean_dec(x_209);
lean_dec(x_2);
x_296 = l___private_Lean_Elab_Match_20__collect___main(x_208, x_7, x_8, x_9);
if (lean_obj_tag(x_296) == 0)
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_296);
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; 
x_298 = lean_ctor_get(x_296, 0);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_298, 0);
x_301 = l_Lean_Syntax_setArg(x_205, x_207, x_300);
x_302 = lean_array_set(x_5, x_12, x_301);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_3);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set(x_298, 0, x_303);
return x_296;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_304 = lean_ctor_get(x_298, 0);
x_305 = lean_ctor_get(x_298, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_298);
x_306 = l_Lean_Syntax_setArg(x_205, x_207, x_304);
x_307 = lean_array_set(x_5, x_12, x_306);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_3);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_305);
lean_ctor_set(x_296, 0, x_309);
return x_296;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_310 = lean_ctor_get(x_296, 0);
x_311 = lean_ctor_get(x_296, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_296);
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_314 = x_310;
} else {
 lean_dec_ref(x_310);
 x_314 = lean_box(0);
}
x_315 = l_Lean_Syntax_setArg(x_205, x_207, x_312);
x_316 = lean_array_set(x_5, x_12, x_315);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_3);
lean_ctor_set(x_317, 1, x_316);
if (lean_is_scalar(x_314)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_314;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_313);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_311);
return x_319;
}
}
else
{
uint8_t x_320; 
lean_dec(x_205);
lean_dec(x_5);
lean_dec(x_3);
x_320 = !lean_is_exclusive(x_296);
if (x_320 == 0)
{
return x_296;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_296, 0);
x_322 = lean_ctor_get(x_296, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_296);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_4);
lean_ctor_set(x_324, 1, x_7);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_9);
return x_325;
}
}
}
else
{
lean_object* x_326; uint8_t x_327; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_8, x_9);
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_7);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_ctor_get(x_326, 0);
x_330 = lean_ctor_get(x_7, 1);
x_331 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_329);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_array_push(x_330, x_332);
lean_ctor_set(x_7, 1, x_333);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_329);
lean_ctor_set(x_334, 1, x_7);
lean_ctor_set(x_326, 0, x_334);
return x_326;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_335 = lean_ctor_get(x_326, 0);
x_336 = lean_ctor_get(x_7, 0);
x_337 = lean_ctor_get(x_7, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_7);
x_338 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_335);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_340 = lean_array_push(x_337, x_339);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_336);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_335);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set(x_326, 0, x_342);
return x_326;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_343 = lean_ctor_get(x_326, 0);
x_344 = lean_ctor_get(x_326, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_326);
x_345 = lean_ctor_get(x_7, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_7, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_347 = x_7;
} else {
 lean_dec_ref(x_7);
 x_347 = lean_box(0);
}
x_348 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_343);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_350 = lean_array_push(x_346, x_349);
if (lean_is_scalar(x_347)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_347;
}
lean_ctor_set(x_351, 0, x_345);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_343);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_344);
return x_353;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_354 = l_Lean_Syntax_inhabited;
x_355 = lean_array_get(x_354, x_5, x_12);
x_356 = l_Lean_Syntax_isNone(x_355);
x_357 = lean_unsigned_to_nat(2u);
x_358 = lean_array_get(x_354, x_5, x_357);
x_359 = l_Lean_Syntax_getArgs(x_358);
lean_dec(x_358);
if (x_356 == 0)
{
uint8_t x_400; 
x_400 = 0;
x_360 = x_400;
goto block_399;
}
else
{
uint8_t x_401; 
x_401 = 1;
x_360 = x_401;
goto block_399;
}
block_399:
{
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
lean_dec(x_359);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_361 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
x_362 = l_Lean_Elab_Term_throwErrorAt___rarg(x_355, x_361, x_8, x_9);
lean_dec(x_355);
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
return x_362;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_362, 0);
x_365 = lean_ctor_get(x_362, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_362);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_355);
x_367 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
x_368 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_359, x_367, x_7, x_8, x_9);
lean_dec(x_359);
if (lean_obj_tag(x_368) == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
lean_object* x_370; uint8_t x_371; 
x_370 = lean_ctor_get(x_368, 0);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_372 = lean_ctor_get(x_370, 0);
x_373 = l_Lean_nullKind;
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = lean_array_set(x_5, x_357, x_374);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_3);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set(x_370, 0, x_376);
return x_368;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_377 = lean_ctor_get(x_370, 0);
x_378 = lean_ctor_get(x_370, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_370);
x_379 = l_Lean_nullKind;
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_377);
x_381 = lean_array_set(x_5, x_357, x_380);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_3);
lean_ctor_set(x_382, 1, x_381);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_378);
lean_ctor_set(x_368, 0, x_383);
return x_368;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_384 = lean_ctor_get(x_368, 0);
x_385 = lean_ctor_get(x_368, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_368);
x_386 = lean_ctor_get(x_384, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_384, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_388 = x_384;
} else {
 lean_dec_ref(x_384);
 x_388 = lean_box(0);
}
x_389 = l_Lean_nullKind;
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_386);
x_391 = lean_array_set(x_5, x_357, x_390);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_3);
lean_ctor_set(x_392, 1, x_391);
if (lean_is_scalar(x_388)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_388;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_387);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_385);
return x_394;
}
}
else
{
uint8_t x_395; 
lean_dec(x_5);
lean_dec(x_3);
x_395 = !lean_is_exclusive(x_368);
if (x_395 == 0)
{
return x_368;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_368, 0);
x_397 = lean_ctor_get(x_368, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_368);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
}
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_402 = l_Lean_Syntax_inhabited;
x_403 = lean_array_get(x_402, x_5, x_12);
x_404 = l_Lean_Syntax_getArgs(x_403);
lean_dec(x_403);
x_405 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_406 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_404, x_405, x_7, x_8, x_9);
lean_dec(x_404);
if (lean_obj_tag(x_406) == 0)
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_406);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_ctor_get(x_406, 0);
x_409 = !lean_is_exclusive(x_408);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_410 = lean_ctor_get(x_408, 0);
x_411 = l_Lean_nullKind;
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_410);
x_413 = lean_array_set(x_5, x_12, x_412);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_3);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set(x_408, 0, x_414);
return x_406;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_415 = lean_ctor_get(x_408, 0);
x_416 = lean_ctor_get(x_408, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_408);
x_417 = l_Lean_nullKind;
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_415);
x_419 = lean_array_set(x_5, x_12, x_418);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_3);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_416);
lean_ctor_set(x_406, 0, x_421);
return x_406;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_422 = lean_ctor_get(x_406, 0);
x_423 = lean_ctor_get(x_406, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_406);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_426 = x_422;
} else {
 lean_dec_ref(x_422);
 x_426 = lean_box(0);
}
x_427 = l_Lean_nullKind;
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_424);
x_429 = lean_array_set(x_5, x_12, x_428);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_3);
lean_ctor_set(x_430, 1, x_429);
if (lean_is_scalar(x_426)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_426;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_425);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_423);
return x_432;
}
}
else
{
uint8_t x_433; 
lean_dec(x_5);
lean_dec(x_3);
x_433 = !lean_is_exclusive(x_406);
if (x_433 == 0)
{
return x_406;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_406, 0);
x_435 = lean_ctor_get(x_406, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_406);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_6);
lean_dec(x_4);
x_437 = l_Lean_Syntax_inhabited;
x_438 = lean_unsigned_to_nat(0u);
x_439 = lean_array_get(x_437, x_5, x_438);
x_440 = lean_array_get(x_437, x_5, x_12);
x_441 = l_Lean_Syntax_getArgs(x_440);
lean_dec(x_440);
lean_inc(x_8);
x_442 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_2, x_441, x_438, x_7, x_8, x_9);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = 1;
lean_inc(x_8);
x_447 = l___private_Lean_Elab_Match_16__processIdAux(x_439, x_446, x_445, x_8, x_444);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_ctor_get(x_448, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_448, 1);
lean_inc(x_451);
lean_dec(x_448);
x_452 = x_441;
x_453 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed), 6, 3);
lean_closure_set(x_453, 0, x_450);
lean_closure_set(x_453, 1, x_438);
lean_closure_set(x_453, 2, x_452);
x_454 = x_453;
x_455 = lean_apply_3(x_454, x_451, x_8, x_449);
if (lean_obj_tag(x_455) == 0)
{
uint8_t x_456; 
x_456 = !lean_is_exclusive(x_455);
if (x_456 == 0)
{
lean_object* x_457; uint8_t x_458; 
x_457 = lean_ctor_get(x_455, 0);
x_458 = !lean_is_exclusive(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_459 = lean_ctor_get(x_457, 0);
x_460 = l_Lean_nullKind;
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_459);
x_462 = lean_array_set(x_5, x_12, x_461);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_3);
lean_ctor_set(x_463, 1, x_462);
lean_ctor_set(x_457, 0, x_463);
return x_455;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_464 = lean_ctor_get(x_457, 0);
x_465 = lean_ctor_get(x_457, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_457);
x_466 = l_Lean_nullKind;
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_464);
x_468 = lean_array_set(x_5, x_12, x_467);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_3);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_465);
lean_ctor_set(x_455, 0, x_470);
return x_455;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_471 = lean_ctor_get(x_455, 0);
x_472 = lean_ctor_get(x_455, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_455);
x_473 = lean_ctor_get(x_471, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_475 = x_471;
} else {
 lean_dec_ref(x_471);
 x_475 = lean_box(0);
}
x_476 = l_Lean_nullKind;
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_473);
x_478 = lean_array_set(x_5, x_12, x_477);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_3);
lean_ctor_set(x_479, 1, x_478);
if (lean_is_scalar(x_475)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_475;
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_474);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_472);
return x_481;
}
}
else
{
uint8_t x_482; 
lean_dec(x_5);
lean_dec(x_3);
x_482 = !lean_is_exclusive(x_455);
if (x_482 == 0)
{
return x_455;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_455, 0);
x_484 = lean_ctor_get(x_455, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_455);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
uint8_t x_486; 
lean_dec(x_441);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_486 = !lean_is_exclusive(x_447);
if (x_486 == 0)
{
return x_447;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_447, 0);
x_488 = lean_ctor_get(x_447, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_447);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
lean_dec(x_441);
lean_dec(x_439);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_490 = !lean_is_exclusive(x_442);
if (x_490 == 0)
{
return x_442;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_442, 0);
x_492 = lean_ctor_get(x_442, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_442);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; uint8_t x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; 
x_494 = lean_ctor_get(x_8, 0);
x_495 = lean_ctor_get(x_8, 1);
x_496 = lean_ctor_get(x_8, 2);
x_497 = lean_ctor_get(x_8, 3);
x_498 = lean_ctor_get(x_8, 4);
x_499 = lean_ctor_get(x_8, 5);
x_500 = lean_ctor_get(x_8, 6);
x_501 = lean_ctor_get(x_8, 7);
x_502 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_503 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_504 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_505 = lean_ctor_get(x_8, 9);
lean_inc(x_505);
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
lean_inc(x_496);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_8);
x_506 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_506, 0, x_494);
lean_ctor_set(x_506, 1, x_495);
lean_ctor_set(x_506, 2, x_496);
lean_ctor_set(x_506, 3, x_497);
lean_ctor_set(x_506, 4, x_498);
lean_ctor_set(x_506, 5, x_499);
lean_ctor_set(x_506, 6, x_500);
lean_ctor_set(x_506, 7, x_501);
lean_ctor_set(x_506, 8, x_11);
lean_ctor_set(x_506, 9, x_505);
lean_ctor_set_uint8(x_506, sizeof(void*)*10, x_502);
lean_ctor_set_uint8(x_506, sizeof(void*)*10 + 1, x_503);
lean_ctor_set_uint8(x_506, sizeof(void*)*10 + 2, x_504);
if (x_1 == 0)
{
lean_object* x_507; lean_object* x_508; uint8_t x_509; 
x_507 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_inc(x_2);
x_508 = lean_name_mk_string(x_2, x_507);
x_509 = lean_name_eq(x_3, x_508);
lean_dec(x_508);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_510 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_inc(x_2);
x_511 = lean_name_mk_string(x_2, x_510);
x_512 = lean_name_eq(x_3, x_511);
lean_dec(x_511);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_513 = l_Lean_mkHole___closed__1;
lean_inc(x_2);
x_514 = lean_name_mk_string(x_2, x_513);
x_515 = lean_name_eq(x_3, x_514);
lean_dec(x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_516 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
lean_inc(x_2);
x_517 = lean_name_mk_string(x_2, x_516);
x_518 = lean_name_eq(x_3, x_517);
lean_dec(x_517);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_519 = l_Lean_mkTermIdFromIdent___closed__1;
lean_inc(x_2);
x_520 = lean_name_mk_string(x_2, x_519);
x_521 = lean_name_eq(x_3, x_520);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; uint8_t x_524; 
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_5);
x_522 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
lean_inc(x_2);
x_523 = lean_name_mk_string(x_2, x_522);
x_524 = lean_name_eq(x_3, x_523);
lean_dec(x_523);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_525 = l_Lean_String_HasQuote___closed__1;
lean_inc(x_2);
x_526 = lean_name_mk_string(x_2, x_525);
x_527 = lean_name_eq(x_3, x_526);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_528 = l_Lean_Nat_HasQuote___closed__1;
lean_inc(x_2);
x_529 = lean_name_mk_string(x_2, x_528);
x_530 = lean_name_eq(x_3, x_529);
lean_dec(x_529);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_531 = l_Lean_Parser_Term_char___elambda__1___closed__1;
x_532 = lean_name_mk_string(x_2, x_531);
x_533 = lean_name_eq(x_3, x_532);
lean_dec(x_532);
if (x_533 == 0)
{
lean_object* x_534; uint8_t x_535; 
lean_dec(x_4);
x_534 = l_Lean_choiceKind;
x_535 = lean_name_eq(x_3, x_534);
lean_dec(x_3);
if (x_535 == 0)
{
lean_object* x_536; 
x_536 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_506, x_9);
lean_dec(x_7);
return x_536;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_7);
x_537 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
x_538 = l_Lean_Elab_Term_throwError___rarg(x_537, x_506, x_9);
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
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; 
lean_dec(x_506);
lean_dec(x_3);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_4);
lean_ctor_set(x_543, 1, x_7);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_9);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_506);
lean_dec(x_3);
lean_dec(x_2);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_4);
lean_ctor_set(x_545, 1, x_7);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_9);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_506);
lean_dec(x_3);
lean_dec(x_2);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_4);
lean_ctor_set(x_547, 1, x_7);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_9);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_506);
lean_dec(x_3);
lean_dec(x_2);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_4);
lean_ctor_set(x_549, 1, x_7);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_9);
return x_550;
}
}
else
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; 
lean_dec(x_3);
x_551 = l_Lean_Syntax_inhabited;
x_552 = lean_array_get(x_551, x_5, x_12);
lean_dec(x_5);
x_553 = l_Lean_Syntax_isNone(x_552);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; 
x_554 = lean_unsigned_to_nat(0u);
x_555 = l_Lean_Syntax_getArg(x_552, x_554);
lean_dec(x_552);
x_556 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_inc(x_2);
x_557 = lean_name_mk_string(x_2, x_556);
lean_inc(x_555);
x_558 = l_Lean_Syntax_isOfKind(x_555, x_557);
lean_dec(x_557);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_559 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_560 = lean_name_mk_string(x_2, x_559);
lean_inc(x_555);
x_561 = l_Lean_Syntax_isOfKind(x_555, x_560);
lean_dec(x_560);
if (x_561 == 0)
{
lean_object* x_562; 
lean_dec(x_555);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_4);
x_562 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_506, x_9);
lean_dec(x_7);
return x_562;
}
else
{
lean_object* x_563; lean_object* x_564; uint8_t x_565; lean_object* x_566; 
x_563 = l_Lean_Syntax_getIdOfTermId(x_4);
x_564 = l_Lean_Syntax_getArg(x_555, x_12);
lean_dec(x_555);
x_565 = 0;
lean_inc(x_506);
lean_inc(x_563);
x_566 = l___private_Lean_Elab_Match_15__processVar(x_563, x_565, x_7, x_506, x_9);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec(x_567);
lean_inc(x_506);
x_570 = l___private_Lean_Elab_Match_20__collect___main(x_564, x_569, x_506, x_568);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = lean_ctor_get(x_571, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_571, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_575 = x_571;
} else {
 lean_dec_ref(x_571);
 x_575 = lean_box(0);
}
x_576 = l_Lean_Elab_Term_getCurrMacroScope(x_506, x_572);
lean_dec(x_506);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = l_Lean_Elab_Term_getMainModule___rarg(x_578);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_582 = x_579;
} else {
 lean_dec_ref(x_579);
 x_582 = lean_box(0);
}
x_583 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_584 = l_Lean_addMacroScope(x_580, x_583, x_577);
x_585 = l_Lean_SourceInfo_inhabited___closed__1;
x_586 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_587 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_588 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_588, 0, x_585);
lean_ctor_set(x_588, 1, x_586);
lean_ctor_set(x_588, 2, x_584);
lean_ctor_set(x_588, 3, x_587);
x_589 = l_Array_empty___closed__1;
x_590 = lean_array_push(x_589, x_588);
x_591 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_592 = lean_array_push(x_590, x_591);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_520);
lean_ctor_set(x_593, 1, x_592);
x_594 = lean_array_push(x_589, x_593);
x_595 = l_Lean_mkTermIdFrom(x_4, x_563);
lean_dec(x_4);
x_596 = lean_array_push(x_589, x_595);
x_597 = lean_array_push(x_596, x_573);
x_598 = l_Lean_nullKind___closed__2;
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_597);
x_600 = lean_array_push(x_594, x_599);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_6);
lean_ctor_set(x_601, 1, x_600);
if (lean_is_scalar(x_575)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_575;
}
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_574);
if (lean_is_scalar(x_582)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_582;
}
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_581);
return x_603;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_563);
lean_dec(x_520);
lean_dec(x_506);
lean_dec(x_6);
lean_dec(x_4);
x_604 = lean_ctor_get(x_570, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_570, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_606 = x_570;
} else {
 lean_dec_ref(x_570);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_520);
lean_dec(x_506);
lean_dec(x_6);
lean_dec(x_4);
x_608 = lean_ctor_get(x_566, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_566, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_610 = x_566;
} else {
 lean_dec_ref(x_566);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
}
else
{
uint8_t x_612; lean_object* x_613; 
lean_dec(x_555);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_2);
x_612 = 1;
lean_inc(x_4);
x_613 = l___private_Lean_Elab_Match_16__processIdAux(x_4, x_612, x_7, x_506, x_9);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_616 = x_613;
} else {
 lean_dec_ref(x_613);
 x_616 = lean_box(0);
}
x_617 = lean_ctor_get(x_614, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_618 = x_614;
} else {
 lean_dec_ref(x_614);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_4);
lean_ctor_set(x_619, 1, x_617);
if (lean_is_scalar(x_616)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_616;
}
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_615);
return x_620;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_4);
x_621 = lean_ctor_get(x_613, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_613, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_623 = x_613;
} else {
 lean_dec_ref(x_613);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
}
else
{
lean_object* x_625; 
lean_dec(x_552);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_2);
lean_inc(x_4);
x_625 = l___private_Lean_Elab_Match_18__processId(x_4, x_7, x_506, x_9);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_628 = x_625;
} else {
 lean_dec_ref(x_625);
 x_628 = lean_box(0);
}
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
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_4);
lean_ctor_set(x_631, 1, x_629);
if (lean_is_scalar(x_628)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_628;
}
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_627);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_4);
x_633 = lean_ctor_get(x_625, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_625, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_635 = x_625;
} else {
 lean_dec_ref(x_625);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
}
}
else
{
lean_object* x_637; lean_object* x_638; uint8_t x_639; 
lean_dec(x_6);
x_637 = l_Lean_Syntax_inhabited;
x_638 = lean_array_get(x_637, x_5, x_12);
x_639 = l_Lean_Syntax_isNone(x_638);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; 
lean_dec(x_4);
x_640 = lean_unsigned_to_nat(0u);
x_641 = l_Lean_Syntax_getArg(x_638, x_640);
x_642 = l_Lean_Syntax_getArg(x_638, x_12);
x_643 = l_Lean_Syntax_isNone(x_642);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; 
x_644 = l_Lean_Syntax_getArg(x_642, x_640);
x_645 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_646 = lean_name_mk_string(x_2, x_645);
lean_inc(x_644);
x_647 = l_Lean_Syntax_isOfKind(x_644, x_646);
lean_dec(x_646);
if (x_647 == 0)
{
lean_object* x_648; 
lean_inc(x_506);
x_648 = l___private_Lean_Elab_Match_20__collect___main(x_641, x_7, x_506, x_9);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
x_651 = lean_ctor_get(x_649, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_649, 1);
lean_inc(x_652);
lean_dec(x_649);
x_653 = l_Lean_Syntax_setArg(x_638, x_640, x_651);
x_654 = l_Lean_Syntax_getArg(x_644, x_12);
x_655 = l_Lean_Syntax_getArgs(x_654);
lean_dec(x_654);
x_656 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_657 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_655, x_656, x_652, x_506, x_650);
lean_dec(x_655);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_660 = x_657;
} else {
 lean_dec_ref(x_657);
 x_660 = lean_box(0);
}
x_661 = lean_ctor_get(x_658, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_658, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_663 = x_658;
} else {
 lean_dec_ref(x_658);
 x_663 = lean_box(0);
}
x_664 = l_Lean_nullKind;
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_661);
x_666 = l_Lean_Syntax_setArg(x_644, x_12, x_665);
x_667 = l_Lean_Syntax_setArg(x_642, x_640, x_666);
x_668 = l_Lean_Syntax_setArg(x_653, x_12, x_667);
x_669 = lean_array_set(x_5, x_12, x_668);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_3);
lean_ctor_set(x_670, 1, x_669);
if (lean_is_scalar(x_663)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_663;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_662);
if (lean_is_scalar(x_660)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_660;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_659);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_653);
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_5);
lean_dec(x_3);
x_673 = lean_ctor_get(x_657, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_657, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_675 = x_657;
} else {
 lean_dec_ref(x_657);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_638);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_3);
x_677 = lean_ctor_get(x_648, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_648, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_679 = x_648;
} else {
 lean_dec_ref(x_648);
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
else
{
lean_object* x_681; 
lean_dec(x_644);
lean_dec(x_642);
x_681 = l___private_Lean_Elab_Match_20__collect___main(x_641, x_7, x_506, x_9);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_684 = x_681;
} else {
 lean_dec_ref(x_681);
 x_684 = lean_box(0);
}
x_685 = lean_ctor_get(x_682, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_682, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_687 = x_682;
} else {
 lean_dec_ref(x_682);
 x_687 = lean_box(0);
}
x_688 = l_Lean_Syntax_setArg(x_638, x_640, x_685);
x_689 = lean_array_set(x_5, x_12, x_688);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_3);
lean_ctor_set(x_690, 1, x_689);
if (lean_is_scalar(x_687)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_687;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_686);
if (lean_is_scalar(x_684)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_684;
}
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_683);
return x_692;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_638);
lean_dec(x_5);
lean_dec(x_3);
x_693 = lean_ctor_get(x_681, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_681, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_695 = x_681;
} else {
 lean_dec_ref(x_681);
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
lean_object* x_697; 
lean_dec(x_642);
lean_dec(x_2);
x_697 = l___private_Lean_Elab_Match_20__collect___main(x_641, x_7, x_506, x_9);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_700 = x_697;
} else {
 lean_dec_ref(x_697);
 x_700 = lean_box(0);
}
x_701 = lean_ctor_get(x_698, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_698, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 x_703 = x_698;
} else {
 lean_dec_ref(x_698);
 x_703 = lean_box(0);
}
x_704 = l_Lean_Syntax_setArg(x_638, x_640, x_701);
x_705 = lean_array_set(x_5, x_12, x_704);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_3);
lean_ctor_set(x_706, 1, x_705);
if (lean_is_scalar(x_703)) {
 x_707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_707 = x_703;
}
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_702);
if (lean_is_scalar(x_700)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_700;
}
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_699);
return x_708;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_638);
lean_dec(x_5);
lean_dec(x_3);
x_709 = lean_ctor_get(x_697, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_697, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_711 = x_697;
} else {
 lean_dec_ref(x_697);
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
lean_object* x_713; lean_object* x_714; 
lean_dec(x_638);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_4);
lean_ctor_set(x_713, 1, x_7);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_9);
return x_714;
}
}
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_715 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_506, x_9);
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_718 = x_715;
} else {
 lean_dec_ref(x_715);
 x_718 = lean_box(0);
}
x_719 = lean_ctor_get(x_7, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_7, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_721 = x_7;
} else {
 lean_dec_ref(x_7);
 x_721 = lean_box(0);
}
x_722 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_716);
x_723 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_723, 0, x_722);
x_724 = lean_array_push(x_720, x_723);
if (lean_is_scalar(x_721)) {
 x_725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_725 = x_721;
}
lean_ctor_set(x_725, 0, x_719);
lean_ctor_set(x_725, 1, x_724);
x_726 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_726, 0, x_716);
lean_ctor_set(x_726, 1, x_725);
if (lean_is_scalar(x_718)) {
 x_727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_727 = x_718;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_717);
return x_727;
}
}
else
{
lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_728 = l_Lean_Syntax_inhabited;
x_729 = lean_array_get(x_728, x_5, x_12);
x_730 = l_Lean_Syntax_isNone(x_729);
x_731 = lean_unsigned_to_nat(2u);
x_732 = lean_array_get(x_728, x_5, x_731);
x_733 = l_Lean_Syntax_getArgs(x_732);
lean_dec(x_732);
if (x_730 == 0)
{
uint8_t x_760; 
x_760 = 0;
x_734 = x_760;
goto block_759;
}
else
{
uint8_t x_761; 
x_761 = 1;
x_734 = x_761;
goto block_759;
}
block_759:
{
if (x_734 == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_733);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_735 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
x_736 = l_Lean_Elab_Term_throwErrorAt___rarg(x_729, x_735, x_506, x_9);
lean_dec(x_729);
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
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_729);
x_741 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
x_742 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_733, x_741, x_7, x_506, x_9);
lean_dec(x_733);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_745 = x_742;
} else {
 lean_dec_ref(x_742);
 x_745 = lean_box(0);
}
x_746 = lean_ctor_get(x_743, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_743, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_748 = x_743;
} else {
 lean_dec_ref(x_743);
 x_748 = lean_box(0);
}
x_749 = l_Lean_nullKind;
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_746);
x_751 = lean_array_set(x_5, x_731, x_750);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_3);
lean_ctor_set(x_752, 1, x_751);
if (lean_is_scalar(x_748)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_748;
}
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_747);
if (lean_is_scalar(x_745)) {
 x_754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_754 = x_745;
}
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_744);
return x_754;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_5);
lean_dec(x_3);
x_755 = lean_ctor_get(x_742, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_742, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_757 = x_742;
} else {
 lean_dec_ref(x_742);
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
}
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_762 = l_Lean_Syntax_inhabited;
x_763 = lean_array_get(x_762, x_5, x_12);
x_764 = l_Lean_Syntax_getArgs(x_763);
lean_dec(x_763);
x_765 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_766 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_764, x_765, x_7, x_506, x_9);
lean_dec(x_764);
if (lean_obj_tag(x_766) == 0)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_766)) {
 lean_ctor_release(x_766, 0);
 lean_ctor_release(x_766, 1);
 x_769 = x_766;
} else {
 lean_dec_ref(x_766);
 x_769 = lean_box(0);
}
x_770 = lean_ctor_get(x_767, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_767, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_772 = x_767;
} else {
 lean_dec_ref(x_767);
 x_772 = lean_box(0);
}
x_773 = l_Lean_nullKind;
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_770);
x_775 = lean_array_set(x_5, x_12, x_774);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_3);
lean_ctor_set(x_776, 1, x_775);
if (lean_is_scalar(x_772)) {
 x_777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_777 = x_772;
}
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_771);
if (lean_is_scalar(x_769)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_769;
}
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_768);
return x_778;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_5);
lean_dec(x_3);
x_779 = lean_ctor_get(x_766, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_766, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_766)) {
 lean_ctor_release(x_766, 0);
 lean_ctor_release(x_766, 1);
 x_781 = x_766;
} else {
 lean_dec_ref(x_766);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 2, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_779);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
lean_dec(x_6);
lean_dec(x_4);
x_783 = l_Lean_Syntax_inhabited;
x_784 = lean_unsigned_to_nat(0u);
x_785 = lean_array_get(x_783, x_5, x_784);
x_786 = lean_array_get(x_783, x_5, x_12);
x_787 = l_Lean_Syntax_getArgs(x_786);
lean_dec(x_786);
lean_inc(x_506);
x_788 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_2, x_787, x_784, x_7, x_506, x_9);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; uint8_t x_792; lean_object* x_793; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = 1;
lean_inc(x_506);
x_793 = l___private_Lean_Elab_Match_16__processIdAux(x_785, x_792, x_791, x_506, x_790);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = lean_ctor_get(x_794, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_794, 1);
lean_inc(x_797);
lean_dec(x_794);
x_798 = x_787;
x_799 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed), 6, 3);
lean_closure_set(x_799, 0, x_796);
lean_closure_set(x_799, 1, x_784);
lean_closure_set(x_799, 2, x_798);
x_800 = x_799;
x_801 = lean_apply_3(x_800, x_797, x_506, x_795);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_804 = x_801;
} else {
 lean_dec_ref(x_801);
 x_804 = lean_box(0);
}
x_805 = lean_ctor_get(x_802, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_802, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_807 = x_802;
} else {
 lean_dec_ref(x_802);
 x_807 = lean_box(0);
}
x_808 = l_Lean_nullKind;
x_809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_805);
x_810 = lean_array_set(x_5, x_12, x_809);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_3);
lean_ctor_set(x_811, 1, x_810);
if (lean_is_scalar(x_807)) {
 x_812 = lean_alloc_ctor(0, 2, 0);
} else {
 x_812 = x_807;
}
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_806);
if (lean_is_scalar(x_804)) {
 x_813 = lean_alloc_ctor(0, 2, 0);
} else {
 x_813 = x_804;
}
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_803);
return x_813;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_5);
lean_dec(x_3);
x_814 = lean_ctor_get(x_801, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_801, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_816 = x_801;
} else {
 lean_dec_ref(x_801);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(1, 2, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_814);
lean_ctor_set(x_817, 1, x_815);
return x_817;
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
lean_dec(x_787);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_3);
x_818 = lean_ctor_get(x_793, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_793, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_820 = x_793;
} else {
 lean_dec_ref(x_793);
 x_820 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_821 = x_820;
}
lean_ctor_set(x_821, 0, x_818);
lean_ctor_set(x_821, 1, x_819);
return x_821;
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_787);
lean_dec(x_785);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_3);
x_822 = lean_ctor_get(x_788, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_788, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_824 = x_788;
} else {
 lean_dec_ref(x_788);
 x_824 = lean_box(0);
}
if (lean_is_scalar(x_824)) {
 x_825 = lean_alloc_ctor(1, 2, 0);
} else {
 x_825 = x_824;
}
lean_ctor_set(x_825, 0, x_822);
lean_ctor_set(x_825, 1, x_823);
return x_825;
}
}
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; uint8_t x_843; uint8_t x_844; uint8_t x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_826 = lean_ctor_get(x_9, 0);
x_827 = lean_ctor_get(x_9, 1);
x_828 = lean_ctor_get(x_9, 2);
x_829 = lean_ctor_get(x_9, 3);
x_830 = lean_ctor_get(x_9, 4);
x_831 = lean_ctor_get(x_9, 5);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_inc(x_828);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_9);
x_832 = lean_unsigned_to_nat(1u);
x_833 = lean_nat_add(x_831, x_832);
x_834 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_834, 0, x_826);
lean_ctor_set(x_834, 1, x_827);
lean_ctor_set(x_834, 2, x_828);
lean_ctor_set(x_834, 3, x_829);
lean_ctor_set(x_834, 4, x_830);
lean_ctor_set(x_834, 5, x_833);
x_835 = lean_ctor_get(x_8, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_8, 1);
lean_inc(x_836);
x_837 = lean_ctor_get(x_8, 2);
lean_inc(x_837);
x_838 = lean_ctor_get(x_8, 3);
lean_inc(x_838);
x_839 = lean_ctor_get(x_8, 4);
lean_inc(x_839);
x_840 = lean_ctor_get(x_8, 5);
lean_inc(x_840);
x_841 = lean_ctor_get(x_8, 6);
lean_inc(x_841);
x_842 = lean_ctor_get(x_8, 7);
lean_inc(x_842);
x_843 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_844 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 1);
x_845 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_846 = lean_ctor_get(x_8, 9);
lean_inc(x_846);
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
 x_847 = x_8;
} else {
 lean_dec_ref(x_8);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(0, 10, 3);
} else {
 x_848 = x_847;
}
lean_ctor_set(x_848, 0, x_835);
lean_ctor_set(x_848, 1, x_836);
lean_ctor_set(x_848, 2, x_837);
lean_ctor_set(x_848, 3, x_838);
lean_ctor_set(x_848, 4, x_839);
lean_ctor_set(x_848, 5, x_840);
lean_ctor_set(x_848, 6, x_841);
lean_ctor_set(x_848, 7, x_842);
lean_ctor_set(x_848, 8, x_831);
lean_ctor_set(x_848, 9, x_846);
lean_ctor_set_uint8(x_848, sizeof(void*)*10, x_843);
lean_ctor_set_uint8(x_848, sizeof(void*)*10 + 1, x_844);
lean_ctor_set_uint8(x_848, sizeof(void*)*10 + 2, x_845);
if (x_1 == 0)
{
lean_object* x_849; lean_object* x_850; uint8_t x_851; 
x_849 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
lean_inc(x_2);
x_850 = lean_name_mk_string(x_2, x_849);
x_851 = lean_name_eq(x_3, x_850);
lean_dec(x_850);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; uint8_t x_854; 
x_852 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
lean_inc(x_2);
x_853 = lean_name_mk_string(x_2, x_852);
x_854 = lean_name_eq(x_3, x_853);
lean_dec(x_853);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; uint8_t x_857; 
x_855 = l_Lean_mkHole___closed__1;
lean_inc(x_2);
x_856 = lean_name_mk_string(x_2, x_855);
x_857 = lean_name_eq(x_3, x_856);
lean_dec(x_856);
if (x_857 == 0)
{
lean_object* x_858; lean_object* x_859; uint8_t x_860; 
x_858 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
lean_inc(x_2);
x_859 = lean_name_mk_string(x_2, x_858);
x_860 = lean_name_eq(x_3, x_859);
lean_dec(x_859);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; uint8_t x_863; 
x_861 = l_Lean_mkTermIdFromIdent___closed__1;
lean_inc(x_2);
x_862 = lean_name_mk_string(x_2, x_861);
x_863 = lean_name_eq(x_3, x_862);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; uint8_t x_866; 
lean_dec(x_862);
lean_dec(x_6);
lean_dec(x_5);
x_864 = l_Lean_Parser_Term_inaccessible___elambda__1___closed__1;
lean_inc(x_2);
x_865 = lean_name_mk_string(x_2, x_864);
x_866 = lean_name_eq(x_3, x_865);
lean_dec(x_865);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; uint8_t x_869; 
x_867 = l_Lean_String_HasQuote___closed__1;
lean_inc(x_2);
x_868 = lean_name_mk_string(x_2, x_867);
x_869 = lean_name_eq(x_3, x_868);
lean_dec(x_868);
if (x_869 == 0)
{
lean_object* x_870; lean_object* x_871; uint8_t x_872; 
x_870 = l_Lean_Nat_HasQuote___closed__1;
lean_inc(x_2);
x_871 = lean_name_mk_string(x_2, x_870);
x_872 = lean_name_eq(x_3, x_871);
lean_dec(x_871);
if (x_872 == 0)
{
lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_873 = l_Lean_Parser_Term_char___elambda__1___closed__1;
x_874 = lean_name_mk_string(x_2, x_873);
x_875 = lean_name_eq(x_3, x_874);
lean_dec(x_874);
if (x_875 == 0)
{
lean_object* x_876; uint8_t x_877; 
lean_dec(x_4);
x_876 = l_Lean_choiceKind;
x_877 = lean_name_eq(x_3, x_876);
lean_dec(x_3);
if (x_877 == 0)
{
lean_object* x_878; 
x_878 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_848, x_834);
lean_dec(x_7);
return x_878;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_7);
x_879 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__3;
x_880 = l_Lean_Elab_Term_throwError___rarg(x_879, x_848, x_834);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_883 = x_880;
} else {
 lean_dec_ref(x_880);
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
else
{
lean_object* x_885; lean_object* x_886; 
lean_dec(x_848);
lean_dec(x_3);
x_885 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_885, 0, x_4);
lean_ctor_set(x_885, 1, x_7);
x_886 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_834);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; 
lean_dec(x_848);
lean_dec(x_3);
lean_dec(x_2);
x_887 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_887, 0, x_4);
lean_ctor_set(x_887, 1, x_7);
x_888 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_888, 0, x_887);
lean_ctor_set(x_888, 1, x_834);
return x_888;
}
}
else
{
lean_object* x_889; lean_object* x_890; 
lean_dec(x_848);
lean_dec(x_3);
lean_dec(x_2);
x_889 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_889, 0, x_4);
lean_ctor_set(x_889, 1, x_7);
x_890 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_834);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_848);
lean_dec(x_3);
lean_dec(x_2);
x_891 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_891, 0, x_4);
lean_ctor_set(x_891, 1, x_7);
x_892 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_834);
return x_892;
}
}
else
{
lean_object* x_893; lean_object* x_894; uint8_t x_895; 
lean_dec(x_3);
x_893 = l_Lean_Syntax_inhabited;
x_894 = lean_array_get(x_893, x_5, x_832);
lean_dec(x_5);
x_895 = l_Lean_Syntax_isNone(x_894);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; uint8_t x_900; 
x_896 = lean_unsigned_to_nat(0u);
x_897 = l_Lean_Syntax_getArg(x_894, x_896);
lean_dec(x_894);
x_898 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_inc(x_2);
x_899 = lean_name_mk_string(x_2, x_898);
lean_inc(x_897);
x_900 = l_Lean_Syntax_isOfKind(x_897, x_899);
lean_dec(x_899);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; uint8_t x_903; 
x_901 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__1;
x_902 = lean_name_mk_string(x_2, x_901);
lean_inc(x_897);
x_903 = l_Lean_Syntax_isOfKind(x_897, x_902);
lean_dec(x_902);
if (x_903 == 0)
{
lean_object* x_904; 
lean_dec(x_897);
lean_dec(x_862);
lean_dec(x_6);
lean_dec(x_4);
x_904 = l___private_Lean_Elab_Match_19__throwInvalidPattern___rarg(x_7, x_848, x_834);
lean_dec(x_7);
return x_904;
}
else
{
lean_object* x_905; lean_object* x_906; uint8_t x_907; lean_object* x_908; 
x_905 = l_Lean_Syntax_getIdOfTermId(x_4);
x_906 = l_Lean_Syntax_getArg(x_897, x_832);
lean_dec(x_897);
x_907 = 0;
lean_inc(x_848);
lean_inc(x_905);
x_908 = l___private_Lean_Elab_Match_15__processVar(x_905, x_907, x_7, x_848, x_834);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
lean_dec(x_909);
lean_inc(x_848);
x_912 = l___private_Lean_Elab_Match_20__collect___main(x_906, x_911, x_848, x_910);
if (lean_obj_tag(x_912) == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = lean_ctor_get(x_913, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_913, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_917 = x_913;
} else {
 lean_dec_ref(x_913);
 x_917 = lean_box(0);
}
x_918 = l_Lean_Elab_Term_getCurrMacroScope(x_848, x_914);
lean_dec(x_848);
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
x_921 = l_Lean_Elab_Term_getMainModule___rarg(x_920);
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_924 = x_921;
} else {
 lean_dec_ref(x_921);
 x_924 = lean_box(0);
}
x_925 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_926 = l_Lean_addMacroScope(x_922, x_925, x_919);
x_927 = l_Lean_SourceInfo_inhabited___closed__1;
x_928 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__5;
x_929 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__8;
x_930 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_930, 0, x_927);
lean_ctor_set(x_930, 1, x_928);
lean_ctor_set(x_930, 2, x_926);
lean_ctor_set(x_930, 3, x_929);
x_931 = l_Array_empty___closed__1;
x_932 = lean_array_push(x_931, x_930);
x_933 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_934 = lean_array_push(x_932, x_933);
x_935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_935, 0, x_862);
lean_ctor_set(x_935, 1, x_934);
x_936 = lean_array_push(x_931, x_935);
x_937 = l_Lean_mkTermIdFrom(x_4, x_905);
lean_dec(x_4);
x_938 = lean_array_push(x_931, x_937);
x_939 = lean_array_push(x_938, x_915);
x_940 = l_Lean_nullKind___closed__2;
x_941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_939);
x_942 = lean_array_push(x_936, x_941);
x_943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_943, 0, x_6);
lean_ctor_set(x_943, 1, x_942);
if (lean_is_scalar(x_917)) {
 x_944 = lean_alloc_ctor(0, 2, 0);
} else {
 x_944 = x_917;
}
lean_ctor_set(x_944, 0, x_943);
lean_ctor_set(x_944, 1, x_916);
if (lean_is_scalar(x_924)) {
 x_945 = lean_alloc_ctor(0, 2, 0);
} else {
 x_945 = x_924;
}
lean_ctor_set(x_945, 0, x_944);
lean_ctor_set(x_945, 1, x_923);
return x_945;
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
lean_dec(x_905);
lean_dec(x_862);
lean_dec(x_848);
lean_dec(x_6);
lean_dec(x_4);
x_946 = lean_ctor_get(x_912, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_912, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_912)) {
 lean_ctor_release(x_912, 0);
 lean_ctor_release(x_912, 1);
 x_948 = x_912;
} else {
 lean_dec_ref(x_912);
 x_948 = lean_box(0);
}
if (lean_is_scalar(x_948)) {
 x_949 = lean_alloc_ctor(1, 2, 0);
} else {
 x_949 = x_948;
}
lean_ctor_set(x_949, 0, x_946);
lean_ctor_set(x_949, 1, x_947);
return x_949;
}
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
lean_dec(x_906);
lean_dec(x_905);
lean_dec(x_862);
lean_dec(x_848);
lean_dec(x_6);
lean_dec(x_4);
x_950 = lean_ctor_get(x_908, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_908, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_908)) {
 lean_ctor_release(x_908, 0);
 lean_ctor_release(x_908, 1);
 x_952 = x_908;
} else {
 lean_dec_ref(x_908);
 x_952 = lean_box(0);
}
if (lean_is_scalar(x_952)) {
 x_953 = lean_alloc_ctor(1, 2, 0);
} else {
 x_953 = x_952;
}
lean_ctor_set(x_953, 0, x_950);
lean_ctor_set(x_953, 1, x_951);
return x_953;
}
}
}
else
{
uint8_t x_954; lean_object* x_955; 
lean_dec(x_897);
lean_dec(x_862);
lean_dec(x_6);
lean_dec(x_2);
x_954 = 1;
lean_inc(x_4);
x_955 = l___private_Lean_Elab_Match_16__processIdAux(x_4, x_954, x_7, x_848, x_834);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 x_958 = x_955;
} else {
 lean_dec_ref(x_955);
 x_958 = lean_box(0);
}
x_959 = lean_ctor_get(x_956, 1);
lean_inc(x_959);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_960 = x_956;
} else {
 lean_dec_ref(x_956);
 x_960 = lean_box(0);
}
if (lean_is_scalar(x_960)) {
 x_961 = lean_alloc_ctor(0, 2, 0);
} else {
 x_961 = x_960;
}
lean_ctor_set(x_961, 0, x_4);
lean_ctor_set(x_961, 1, x_959);
if (lean_is_scalar(x_958)) {
 x_962 = lean_alloc_ctor(0, 2, 0);
} else {
 x_962 = x_958;
}
lean_ctor_set(x_962, 0, x_961);
lean_ctor_set(x_962, 1, x_957);
return x_962;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_4);
x_963 = lean_ctor_get(x_955, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_955, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 x_965 = x_955;
} else {
 lean_dec_ref(x_955);
 x_965 = lean_box(0);
}
if (lean_is_scalar(x_965)) {
 x_966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_966 = x_965;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_964);
return x_966;
}
}
}
else
{
lean_object* x_967; 
lean_dec(x_894);
lean_dec(x_862);
lean_dec(x_6);
lean_dec(x_2);
lean_inc(x_4);
x_967 = l___private_Lean_Elab_Match_18__processId(x_4, x_7, x_848, x_834);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_970 = x_967;
} else {
 lean_dec_ref(x_967);
 x_970 = lean_box(0);
}
x_971 = lean_ctor_get(x_968, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 lean_ctor_release(x_968, 1);
 x_972 = x_968;
} else {
 lean_dec_ref(x_968);
 x_972 = lean_box(0);
}
if (lean_is_scalar(x_972)) {
 x_973 = lean_alloc_ctor(0, 2, 0);
} else {
 x_973 = x_972;
}
lean_ctor_set(x_973, 0, x_4);
lean_ctor_set(x_973, 1, x_971);
if (lean_is_scalar(x_970)) {
 x_974 = lean_alloc_ctor(0, 2, 0);
} else {
 x_974 = x_970;
}
lean_ctor_set(x_974, 0, x_973);
lean_ctor_set(x_974, 1, x_969);
return x_974;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_4);
x_975 = lean_ctor_get(x_967, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_967, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_977 = x_967;
} else {
 lean_dec_ref(x_967);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_977)) {
 x_978 = lean_alloc_ctor(1, 2, 0);
} else {
 x_978 = x_977;
}
lean_ctor_set(x_978, 0, x_975);
lean_ctor_set(x_978, 1, x_976);
return x_978;
}
}
}
}
else
{
lean_object* x_979; lean_object* x_980; uint8_t x_981; 
lean_dec(x_6);
x_979 = l_Lean_Syntax_inhabited;
x_980 = lean_array_get(x_979, x_5, x_832);
x_981 = l_Lean_Syntax_isNone(x_980);
if (x_981 == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; uint8_t x_985; 
lean_dec(x_4);
x_982 = lean_unsigned_to_nat(0u);
x_983 = l_Lean_Syntax_getArg(x_980, x_982);
x_984 = l_Lean_Syntax_getArg(x_980, x_832);
x_985 = l_Lean_Syntax_isNone(x_984);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; uint8_t x_989; 
x_986 = l_Lean_Syntax_getArg(x_984, x_982);
x_987 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__1;
x_988 = lean_name_mk_string(x_2, x_987);
lean_inc(x_986);
x_989 = l_Lean_Syntax_isOfKind(x_986, x_988);
lean_dec(x_988);
if (x_989 == 0)
{
lean_object* x_990; 
lean_inc(x_848);
x_990 = l___private_Lean_Elab_Match_20__collect___main(x_983, x_7, x_848, x_834);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_991 = lean_ctor_get(x_990, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_990, 1);
lean_inc(x_992);
lean_dec(x_990);
x_993 = lean_ctor_get(x_991, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_991, 1);
lean_inc(x_994);
lean_dec(x_991);
x_995 = l_Lean_Syntax_setArg(x_980, x_982, x_993);
x_996 = l_Lean_Syntax_getArg(x_986, x_832);
x_997 = l_Lean_Syntax_getArgs(x_996);
lean_dec(x_996);
x_998 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_999 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_997, x_998, x_994, x_848, x_992);
lean_dec(x_997);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1002 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1002 = lean_box(0);
}
x_1003 = lean_ctor_get(x_1000, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1000, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 lean_ctor_release(x_1000, 1);
 x_1005 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1005 = lean_box(0);
}
x_1006 = l_Lean_nullKind;
x_1007 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_1003);
x_1008 = l_Lean_Syntax_setArg(x_986, x_832, x_1007);
x_1009 = l_Lean_Syntax_setArg(x_984, x_982, x_1008);
x_1010 = l_Lean_Syntax_setArg(x_995, x_832, x_1009);
x_1011 = lean_array_set(x_5, x_832, x_1010);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_3);
lean_ctor_set(x_1012, 1, x_1011);
if (lean_is_scalar(x_1005)) {
 x_1013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1013 = x_1005;
}
lean_ctor_set(x_1013, 0, x_1012);
lean_ctor_set(x_1013, 1, x_1004);
if (lean_is_scalar(x_1002)) {
 x_1014 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1014 = x_1002;
}
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_1001);
return x_1014;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_995);
lean_dec(x_986);
lean_dec(x_984);
lean_dec(x_5);
lean_dec(x_3);
x_1015 = lean_ctor_get(x_999, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_999, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1017 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1017 = lean_box(0);
}
if (lean_is_scalar(x_1017)) {
 x_1018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1018 = x_1017;
}
lean_ctor_set(x_1018, 0, x_1015);
lean_ctor_set(x_1018, 1, x_1016);
return x_1018;
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
lean_dec(x_986);
lean_dec(x_984);
lean_dec(x_980);
lean_dec(x_848);
lean_dec(x_5);
lean_dec(x_3);
x_1019 = lean_ctor_get(x_990, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_990, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_990)) {
 lean_ctor_release(x_990, 0);
 lean_ctor_release(x_990, 1);
 x_1021 = x_990;
} else {
 lean_dec_ref(x_990);
 x_1021 = lean_box(0);
}
if (lean_is_scalar(x_1021)) {
 x_1022 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1022 = x_1021;
}
lean_ctor_set(x_1022, 0, x_1019);
lean_ctor_set(x_1022, 1, x_1020);
return x_1022;
}
}
else
{
lean_object* x_1023; 
lean_dec(x_986);
lean_dec(x_984);
x_1023 = l___private_Lean_Elab_Match_20__collect___main(x_983, x_7, x_848, x_834);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1023, 1);
lean_inc(x_1025);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 x_1026 = x_1023;
} else {
 lean_dec_ref(x_1023);
 x_1026 = lean_box(0);
}
x_1027 = lean_ctor_get(x_1024, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1024, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 lean_ctor_release(x_1024, 1);
 x_1029 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1029 = lean_box(0);
}
x_1030 = l_Lean_Syntax_setArg(x_980, x_982, x_1027);
x_1031 = lean_array_set(x_5, x_832, x_1030);
x_1032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1032, 0, x_3);
lean_ctor_set(x_1032, 1, x_1031);
if (lean_is_scalar(x_1029)) {
 x_1033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1033 = x_1029;
}
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_1028);
if (lean_is_scalar(x_1026)) {
 x_1034 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1034 = x_1026;
}
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1025);
return x_1034;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_980);
lean_dec(x_5);
lean_dec(x_3);
x_1035 = lean_ctor_get(x_1023, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1023, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 x_1037 = x_1023;
} else {
 lean_dec_ref(x_1023);
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
else
{
lean_object* x_1039; 
lean_dec(x_984);
lean_dec(x_2);
x_1039 = l___private_Lean_Elab_Match_20__collect___main(x_983, x_7, x_848, x_834);
if (lean_obj_tag(x_1039) == 0)
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_1039)) {
 lean_ctor_release(x_1039, 0);
 lean_ctor_release(x_1039, 1);
 x_1042 = x_1039;
} else {
 lean_dec_ref(x_1039);
 x_1042 = lean_box(0);
}
x_1043 = lean_ctor_get(x_1040, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1040, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1045 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1045 = lean_box(0);
}
x_1046 = l_Lean_Syntax_setArg(x_980, x_982, x_1043);
x_1047 = lean_array_set(x_5, x_832, x_1046);
x_1048 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1048, 0, x_3);
lean_ctor_set(x_1048, 1, x_1047);
if (lean_is_scalar(x_1045)) {
 x_1049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1049 = x_1045;
}
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_1044);
if (lean_is_scalar(x_1042)) {
 x_1050 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1050 = x_1042;
}
lean_ctor_set(x_1050, 0, x_1049);
lean_ctor_set(x_1050, 1, x_1041);
return x_1050;
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_980);
lean_dec(x_5);
lean_dec(x_3);
x_1051 = lean_ctor_get(x_1039, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1039, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_1039)) {
 lean_ctor_release(x_1039, 0);
 lean_ctor_release(x_1039, 1);
 x_1053 = x_1039;
} else {
 lean_dec_ref(x_1039);
 x_1053 = lean_box(0);
}
if (lean_is_scalar(x_1053)) {
 x_1054 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1054 = x_1053;
}
lean_ctor_set(x_1054, 0, x_1051);
lean_ctor_set(x_1054, 1, x_1052);
return x_1054;
}
}
}
else
{
lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_980);
lean_dec(x_848);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_1055 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1055, 0, x_4);
lean_ctor_set(x_1055, 1, x_7);
x_1056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_834);
return x_1056;
}
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1057 = l___private_Lean_Elab_Match_10__mkMVarSyntax(x_848, x_834);
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
x_1061 = lean_ctor_get(x_7, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_7, 1);
lean_inc(x_1062);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_1063 = x_7;
} else {
 lean_dec_ref(x_7);
 x_1063 = lean_box(0);
}
x_1064 = l___private_Lean_Elab_Match_11__getMVarSyntaxMVarId(x_1058);
x_1065 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1065, 0, x_1064);
x_1066 = lean_array_push(x_1062, x_1065);
if (lean_is_scalar(x_1063)) {
 x_1067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1067 = x_1063;
}
lean_ctor_set(x_1067, 0, x_1061);
lean_ctor_set(x_1067, 1, x_1066);
x_1068 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1068, 0, x_1058);
lean_ctor_set(x_1068, 1, x_1067);
if (lean_is_scalar(x_1060)) {
 x_1069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1069 = x_1060;
}
lean_ctor_set(x_1069, 0, x_1068);
lean_ctor_set(x_1069, 1, x_1059);
return x_1069;
}
}
else
{
lean_object* x_1070; lean_object* x_1071; uint8_t x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1076; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1070 = l_Lean_Syntax_inhabited;
x_1071 = lean_array_get(x_1070, x_5, x_832);
x_1072 = l_Lean_Syntax_isNone(x_1071);
x_1073 = lean_unsigned_to_nat(2u);
x_1074 = lean_array_get(x_1070, x_5, x_1073);
x_1075 = l_Lean_Syntax_getArgs(x_1074);
lean_dec(x_1074);
if (x_1072 == 0)
{
uint8_t x_1102; 
x_1102 = 0;
x_1076 = x_1102;
goto block_1101;
}
else
{
uint8_t x_1103; 
x_1103 = 1;
x_1076 = x_1103;
goto block_1101;
}
block_1101:
{
if (x_1076 == 0)
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_1075);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_1077 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__12;
x_1078 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1071, x_1077, x_848, x_834);
lean_dec(x_1071);
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1078, 1);
lean_inc(x_1080);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 x_1081 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1081 = lean_box(0);
}
if (lean_is_scalar(x_1081)) {
 x_1082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1082 = x_1081;
}
lean_ctor_set(x_1082, 0, x_1079);
lean_ctor_set(x_1082, 1, x_1080);
return x_1082;
}
else
{
lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_1071);
x_1083 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__13;
x_1084 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1075, x_1083, x_7, x_848, x_834);
lean_dec(x_1075);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1087 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1087 = lean_box(0);
}
x_1088 = lean_ctor_get(x_1085, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1085, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 lean_ctor_release(x_1085, 1);
 x_1090 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1090 = lean_box(0);
}
x_1091 = l_Lean_nullKind;
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1091);
lean_ctor_set(x_1092, 1, x_1088);
x_1093 = lean_array_set(x_5, x_1073, x_1092);
x_1094 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1094, 0, x_3);
lean_ctor_set(x_1094, 1, x_1093);
if (lean_is_scalar(x_1090)) {
 x_1095 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1095 = x_1090;
}
lean_ctor_set(x_1095, 0, x_1094);
lean_ctor_set(x_1095, 1, x_1089);
if (lean_is_scalar(x_1087)) {
 x_1096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1096 = x_1087;
}
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1086);
return x_1096;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_5);
lean_dec(x_3);
x_1097 = lean_ctor_get(x_1084, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1084, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1099 = x_1084;
} else {
 lean_dec_ref(x_1084);
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
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1104 = l_Lean_Syntax_inhabited;
x_1105 = lean_array_get(x_1104, x_5, x_832);
x_1106 = l_Lean_Syntax_getArgs(x_1105);
lean_dec(x_1105);
x_1107 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__9;
x_1108 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_20__collect___main___spec__1(x_1106, x_1107, x_7, x_848, x_834);
lean_dec(x_1106);
if (lean_obj_tag(x_1108) == 0)
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_1108)) {
 lean_ctor_release(x_1108, 0);
 lean_ctor_release(x_1108, 1);
 x_1111 = x_1108;
} else {
 lean_dec_ref(x_1108);
 x_1111 = lean_box(0);
}
x_1112 = lean_ctor_get(x_1109, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1109, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1109)) {
 lean_ctor_release(x_1109, 0);
 lean_ctor_release(x_1109, 1);
 x_1114 = x_1109;
} else {
 lean_dec_ref(x_1109);
 x_1114 = lean_box(0);
}
x_1115 = l_Lean_nullKind;
x_1116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1116, 0, x_1115);
lean_ctor_set(x_1116, 1, x_1112);
x_1117 = lean_array_set(x_5, x_832, x_1116);
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_3);
lean_ctor_set(x_1118, 1, x_1117);
if (lean_is_scalar(x_1114)) {
 x_1119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1119 = x_1114;
}
lean_ctor_set(x_1119, 0, x_1118);
lean_ctor_set(x_1119, 1, x_1113);
if (lean_is_scalar(x_1111)) {
 x_1120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1120 = x_1111;
}
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1120, 1, x_1110);
return x_1120;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_5);
lean_dec(x_3);
x_1121 = lean_ctor_get(x_1108, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1108, 1);
lean_inc(x_1122);
if (lean_is_exclusive(x_1108)) {
 lean_ctor_release(x_1108, 0);
 lean_ctor_release(x_1108, 1);
 x_1123 = x_1108;
} else {
 lean_dec_ref(x_1108);
 x_1123 = lean_box(0);
}
if (lean_is_scalar(x_1123)) {
 x_1124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1124 = x_1123;
}
lean_ctor_set(x_1124, 0, x_1121);
lean_ctor_set(x_1124, 1, x_1122);
return x_1124;
}
}
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
lean_dec(x_6);
lean_dec(x_4);
x_1125 = l_Lean_Syntax_inhabited;
x_1126 = lean_unsigned_to_nat(0u);
x_1127 = lean_array_get(x_1125, x_5, x_1126);
x_1128 = lean_array_get(x_1125, x_5, x_832);
x_1129 = l_Lean_Syntax_getArgs(x_1128);
lean_dec(x_1128);
lean_inc(x_848);
x_1130 = l_Array_forMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__3(x_2, x_1129, x_1126, x_7, x_848, x_834);
if (lean_obj_tag(x_1130) == 0)
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; lean_object* x_1135; 
x_1131 = lean_ctor_get(x_1130, 0);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1130, 1);
lean_inc(x_1132);
lean_dec(x_1130);
x_1133 = lean_ctor_get(x_1131, 1);
lean_inc(x_1133);
lean_dec(x_1131);
x_1134 = 1;
lean_inc(x_848);
x_1135 = l___private_Lean_Elab_Match_16__processIdAux(x_1127, x_1134, x_1133, x_848, x_1132);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
x_1137 = lean_ctor_get(x_1135, 1);
lean_inc(x_1137);
lean_dec(x_1135);
x_1138 = lean_ctor_get(x_1136, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1136, 1);
lean_inc(x_1139);
lean_dec(x_1136);
x_1140 = x_1129;
x_1141 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_20__collect___main___spec__4___boxed), 6, 3);
lean_closure_set(x_1141, 0, x_1138);
lean_closure_set(x_1141, 1, x_1126);
lean_closure_set(x_1141, 2, x_1140);
x_1142 = x_1141;
x_1143 = lean_apply_3(x_1142, x_1139, x_848, x_1137);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1143, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 lean_ctor_release(x_1143, 1);
 x_1146 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1146 = lean_box(0);
}
x_1147 = lean_ctor_get(x_1144, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1144, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 lean_ctor_release(x_1144, 1);
 x_1149 = x_1144;
} else {
 lean_dec_ref(x_1144);
 x_1149 = lean_box(0);
}
x_1150 = l_Lean_nullKind;
x_1151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1151, 0, x_1150);
lean_ctor_set(x_1151, 1, x_1147);
x_1152 = lean_array_set(x_5, x_832, x_1151);
x_1153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1153, 0, x_3);
lean_ctor_set(x_1153, 1, x_1152);
if (lean_is_scalar(x_1149)) {
 x_1154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1154 = x_1149;
}
lean_ctor_set(x_1154, 0, x_1153);
lean_ctor_set(x_1154, 1, x_1148);
if (lean_is_scalar(x_1146)) {
 x_1155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1155 = x_1146;
}
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_1145);
return x_1155;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_5);
lean_dec(x_3);
x_1156 = lean_ctor_get(x_1143, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1143, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 lean_ctor_release(x_1143, 1);
 x_1158 = x_1143;
} else {
 lean_dec_ref(x_1143);
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
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
lean_dec(x_1129);
lean_dec(x_848);
lean_dec(x_5);
lean_dec(x_3);
x_1160 = lean_ctor_get(x_1135, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1135, 1);
lean_inc(x_1161);
if (lean_is_exclusive(x_1135)) {
 lean_ctor_release(x_1135, 0);
 lean_ctor_release(x_1135, 1);
 x_1162 = x_1135;
} else {
 lean_dec_ref(x_1135);
 x_1162 = lean_box(0);
}
if (lean_is_scalar(x_1162)) {
 x_1163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1163 = x_1162;
}
lean_ctor_set(x_1163, 0, x_1160);
lean_ctor_set(x_1163, 1, x_1161);
return x_1163;
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
lean_dec(x_1129);
lean_dec(x_1127);
lean_dec(x_848);
lean_dec(x_5);
lean_dec(x_3);
x_1164 = lean_ctor_get(x_1130, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1130, 1);
lean_inc(x_1165);
if (lean_is_exclusive(x_1130)) {
 lean_ctor_release(x_1130, 0);
 lean_ctor_release(x_1130, 1);
 x_1166 = x_1130;
} else {
 lean_dec_ref(x_1130);
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
lean_closure_set(x_12, 4, x_6);
lean_closure_set(x_12, 5, x_7);
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
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_18__processNonVariable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("collecting variables at pattern: ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
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
x_18 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
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
x_35 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_mkFVar(x_13);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_inferType(x_14, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_3);
x_21 = l_Lean_Elab_Term_mkFreshExprMVarWithId(x_12, x_18, x_19, x_20, x_3, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_2 = x_11;
x_4 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_9);
x_2 = x_11;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
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
x_18 = 1;
lean_inc(x_5);
lean_inc(x_17);
lean_inc(x_16);
x_19 = l_Lean_Elab_Term_elabTerm(x_16, x_17, x_18, x_5, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_5, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_5, 8);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_34 = lean_ctor_get(x_5, 9);
lean_inc(x_34);
x_35 = l_Lean_Elab_replaceRef(x_16, x_34);
lean_dec(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set(x_36, 4, x_26);
lean_ctor_set(x_36, 5, x_27);
lean_ctor_set(x_36, 6, x_28);
lean_ctor_set(x_36, 7, x_29);
lean_ctor_set(x_36, 8, x_30);
lean_ctor_set(x_36, 9, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*10, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*10 + 1, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*10 + 2, x_33);
x_37 = l_Lean_Elab_Term_ensureHasType(x_17, x_20, x_36, x_21);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_2, x_40);
lean_dec(x_2);
x_42 = lean_expr_instantiate1(x_15, x_38);
lean_dec(x_15);
x_43 = lean_array_push(x_4, x_38);
x_2 = x_41;
x_3 = x_42;
x_4 = x_43;
x_6 = x_39;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
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
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_dec(x_11);
x_54 = l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3;
x_55 = l_Lean_Elab_Term_throwError___rarg(x_54, x_5, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_13);
x_15 = l_Lean_Elab_Term_isExprMVarAssigned(x_13, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_14);
x_19 = l_Lean_mkFVar(x_14);
x_20 = l_Lean_Elab_Term_assignExprMVar(x_13, x_19, x_5, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_5);
x_22 = l_Lean_Elab_Term_getLocalDecl(x_14, x_5, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_push(x_4, x_23);
x_3 = x_12;
x_4 = x_25;
x_6 = x_24;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_13);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_3 = x_12;
x_6 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_10, 0);
lean_inc(x_33);
lean_dec(x_10);
lean_inc(x_5);
x_34 = l_Lean_Elab_Term_getLocalDecl(x_33, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_push(x_4, x_35);
x_3 = x_12;
x_4 = x_37;
x_6 = x_36;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_NameSet_contains(x_2, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
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
lean_object* l___private_Lean_Elab_Match_29__getFieldsBinderInfo(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Match_29__getFieldsBinderInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_29__getFieldsBinderInfo(x_1);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_10 = x_4;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_13 = lean_array_fget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_fset(x_4, x_3, x_14);
x_26 = x_13;
x_31 = l_Lean_BinderInfo_inhabited;
x_32 = lean_box(x_31);
x_33 = lean_array_get(x_32, x_2, x_3);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
x_35 = l_Lean_BinderInfo_isExplicit(x_34);
if (x_35 == 0)
{
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_1);
x_38 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__2(x_1, x_36, x_1, x_37, x_14);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
x_39 = lean_box(0);
x_27 = x_39;
goto block_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = l___private_Lean_Elab_Match_25__alreadyVisited(x_36, x_5, x_6, x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lean_Expr_fvarId_x21(x_26);
lean_dec(x_26);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l___private_Lean_Elab_Match_26__markAsVisited(x_36, x_45, x_6, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
lean_ctor_set(x_49, 0, x_47);
x_16 = x_49;
x_17 = x_50;
goto block_25;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_16 = x_54;
x_17 = x_50;
goto block_25;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_36);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_41, 0);
lean_dec(x_57);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_41, 0, x_58);
x_16 = x_41;
x_17 = x_55;
goto block_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_26);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_16 = x_61;
x_17 = x_55;
goto block_25;
}
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_30;
}
}
else
{
lean_object* x_63; 
lean_inc(x_6);
lean_inc(x_1);
x_63 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_26, x_5, x_6, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_16 = x_64;
x_17 = x_65;
goto block_25;
}
else
{
uint8_t x_66; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
block_25:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_15, x_3, x_22);
lean_dec(x_3);
x_3 = x_21;
x_4 = x_23;
x_5 = x_19;
x_7 = x_17;
goto _start;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_16 = x_29;
x_17 = x_7;
goto block_25;
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
lean_object* l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_10, x_3, x_4, x_5);
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
x_17 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_1, x_11, x_16, x_4, x_14);
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
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_19, 0, x_2);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_29 = x_25;
} else {
 lean_dec_ref(x_25);
 x_29 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_15);
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_15);
lean_free_object(x_2);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_1);
x_42 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_40, x_3, x_4, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_1, x_41, x_46, x_4, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_45);
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_59 = x_47;
} else {
 lean_dec_ref(x_47);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_1);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_63 = x_42;
} else {
 lean_dec_ref(x_42);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
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
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_inaccessible_x3f(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Expr_arrayLit_x3f(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l___private_Lean_Elab_Match_20__collect___main___lambda__2___closed__6;
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity___main(x_2, x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isNatLit(x_2);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isStringLit(x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isCharLit(x_2);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isFVar(x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_whnf(x_2, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_expr_eqv(x_16, x_2);
if (x_18 == 0)
{
lean_dec(x_2);
x_2 = x_16;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_16);
x_20 = l_Lean_Expr_getAppFn___main(x_2);
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
lean_dec(x_1);
x_27 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_2, x_3, x_4, x_25);
lean_dec(x_3);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_30);
x_32 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
lean_inc(x_2);
x_36 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_33, x_35);
x_37 = lean_array_get_size(x_36);
x_38 = lean_ctor_get(x_29, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 4);
lean_inc(x_39);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_39);
x_41 = lean_nat_dec_eq(x_37, x_40);
lean_dec(x_40);
x_42 = l_Array_extract___rarg(x_36, x_30, x_38);
x_43 = l_Array_extract___rarg(x_36, x_38, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_44 = l___private_Lean_Elab_Match_29__getFieldsBinderInfo(x_29);
lean_dec(x_29);
x_45 = x_43;
x_46 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed), 7, 4);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_44);
lean_closure_set(x_46, 2, x_30);
lean_closure_set(x_46, 3, x_45);
if (x_41 == 0)
{
uint8_t x_83; 
x_83 = 0;
x_47 = x_83;
goto block_82;
}
else
{
uint8_t x_84; 
x_84 = 1;
x_47 = x_84;
goto block_82;
}
block_82:
{
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_22);
lean_dec(x_21);
x_48 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_2, x_3, x_4, x_25);
lean_dec(x_3);
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
lean_dec(x_2);
x_53 = x_46;
x_54 = lean_apply_3(x_53, x_3, x_4, x_25);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l_Array_toList___rarg(x_42);
lean_dec(x_42);
x_60 = l_Array_toList___rarg(x_58);
lean_dec(x_58);
x_61 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_61, 0, x_21);
lean_ctor_set(x_61, 1, x_22);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_56, 0, x_61);
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = l_Array_toList___rarg(x_42);
lean_dec(x_42);
x_65 = l_Array_toList___rarg(x_62);
lean_dec(x_62);
x_66 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_66, 0, x_21);
lean_ctor_set(x_66, 1, x_22);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_54, 0, x_67);
return x_54;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_54, 0);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_54);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
x_73 = l_Array_toList___rarg(x_42);
lean_dec(x_42);
x_74 = l_Array_toList___rarg(x_70);
lean_dec(x_70);
x_75 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_75, 0, x_21);
lean_ctor_set(x_75, 1, x_22);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_74);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_42);
lean_dec(x_22);
lean_dec(x_21);
x_78 = !lean_is_exclusive(x_54);
if (x_78 == 0)
{
return x_54;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_54, 0);
x_80 = lean_ctor_get(x_54, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_54);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
x_85 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_2, x_3, x_4, x_25);
lean_dec(x_3);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_20);
lean_dec(x_1);
x_86 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_2, x_3, x_4, x_17);
lean_dec(x_3);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_15);
if (x_87 == 0)
{
return x_15;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_15, 0);
x_89 = lean_ctor_get(x_15, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_15);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; 
x_91 = l_Lean_Expr_fvarId_x21(x_2);
x_92 = lean_array_get_size(x_1);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__4(x_1, x_91, x_1, x_92, x_93);
lean_dec(x_92);
lean_dec(x_1);
if (x_94 == 0)
{
uint8_t x_136; 
x_136 = 0;
x_95 = x_136;
goto block_135;
}
else
{
uint8_t x_137; 
x_137 = 1;
x_95 = x_137;
goto block_135;
}
block_135:
{
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
lean_dec(x_91);
x_96 = l___private_Lean_Elab_Match_27__throwInvalidPattern___rarg(x_2, x_3, x_4, x_5);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = l___private_Lean_Elab_Match_25__alreadyVisited(x_91, x_3, x_4, x_5);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_2);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
lean_inc(x_91);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_91);
x_108 = l___private_Lean_Elab_Match_26__markAsVisited(x_91, x_106, x_4, x_105);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
lean_ctor_set(x_110, 0, x_107);
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_108, 0, x_114);
return x_108;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_108, 0);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_108);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_116);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_91);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_101);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_101, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_102);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_102, 0);
lean_dec(x_124);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_2);
lean_ctor_set(x_102, 0, x_125);
return x_101;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_102, 1);
lean_inc(x_126);
lean_dec(x_102);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_2);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_101, 0, x_128);
return x_101;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_101, 1);
lean_inc(x_129);
lean_dec(x_101);
x_130 = lean_ctor_get(x_102, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_131 = x_102;
} else {
 lean_dec_ref(x_102);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_2);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_4);
lean_dec(x_1);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_2);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_5);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_4);
lean_dec(x_1);
x_141 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_141, 0, x_2);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_3);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_5);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_4);
lean_dec(x_1);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_3);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_5);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_147);
x_149 = lean_unsigned_to_nat(2u);
x_150 = lean_nat_sub(x_148, x_149);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_sub(x_150, x_151);
lean_dec(x_150);
x_153 = l_Lean_Expr_getRevArg_x21___main(x_2, x_152);
lean_inc(x_4);
x_154 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_153, x_3, x_4, x_5);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_154, 1);
x_159 = lean_ctor_get(x_156, 0);
x_160 = lean_ctor_get(x_156, 1);
x_161 = lean_nat_sub(x_148, x_151);
lean_dec(x_148);
x_162 = lean_nat_sub(x_161, x_151);
lean_dec(x_161);
x_163 = l_Lean_Expr_getRevArg_x21___main(x_2, x_162);
lean_dec(x_2);
if (lean_obj_tag(x_163) == 1)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_4);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set(x_156, 0, x_165);
return x_154;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_163);
lean_free_object(x_156);
lean_dec(x_160);
lean_dec(x_159);
lean_free_object(x_154);
x_166 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_167 = l_Lean_Elab_Term_throwError___rarg(x_166, x_4, x_158);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
return x_167;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_167);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_154, 1);
x_173 = lean_ctor_get(x_156, 0);
x_174 = lean_ctor_get(x_156, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_156);
x_175 = lean_nat_sub(x_148, x_151);
lean_dec(x_148);
x_176 = lean_nat_sub(x_175, x_151);
lean_dec(x_175);
x_177 = l_Lean_Expr_getRevArg_x21___main(x_2, x_176);
lean_dec(x_2);
if (lean_obj_tag(x_177) == 1)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_4);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_173);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
lean_ctor_set(x_154, 0, x_180);
return x_154;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_177);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_154);
x_181 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_182 = l_Lean_Elab_Term_throwError___rarg(x_181, x_4, x_172);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
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
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_154, 0);
x_188 = lean_ctor_get(x_154, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_154);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_nat_sub(x_148, x_151);
lean_dec(x_148);
x_193 = lean_nat_sub(x_192, x_151);
lean_dec(x_192);
x_194 = l_Lean_Expr_getRevArg_x21___main(x_2, x_193);
lean_dec(x_2);
if (lean_obj_tag(x_194) == 1)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_4);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_189);
if (lean_is_scalar(x_191)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_191;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_188);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_194);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
x_199 = l_Lean_Elab_Term_ToDepElimPattern_main___main___closed__3;
x_200 = l_Lean_Elab_Term_throwError___rarg(x_199, x_4, x_188);
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
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_148);
lean_dec(x_4);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_154);
if (x_205 == 0)
{
return x_154;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_154, 0);
x_207 = lean_ctor_get(x_154, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_154);
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
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_2);
x_209 = lean_ctor_get(x_7, 0);
lean_inc(x_209);
lean_dec(x_7);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_List_mapM___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__5(x_1, x_211, x_3, x_4, x_5);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_214, 0, x_217);
return x_212;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_214, 0);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_214);
x_220 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_220, 0, x_210);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set(x_212, 0, x_221);
return x_212;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_212, 0);
x_223 = lean_ctor_get(x_212, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_212);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
x_227 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_227, 0, x_210);
lean_ctor_set(x_227, 1, x_224);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_223);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_210);
x_230 = !lean_is_exclusive(x_212);
if (x_230 == 0)
{
return x_212;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_212, 0);
x_232 = lean_ctor_get(x_212, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_212);
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
lean_object* x_234; lean_object* x_235; 
lean_dec(x_2);
x_234 = lean_ctor_get(x_6, 0);
lean_inc(x_234);
lean_dec(x_6);
if (lean_obj_tag(x_234) == 1)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_234, 0);
lean_inc(x_240);
x_241 = lean_array_get_size(x_1);
x_242 = lean_unsigned_to_nat(0u);
x_243 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__6(x_1, x_240, x_1, x_241, x_242);
lean_dec(x_241);
lean_dec(x_1);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_240);
lean_dec(x_4);
x_244 = lean_box(0);
x_235 = x_244;
goto block_239;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_245 = l___private_Lean_Elab_Match_25__alreadyVisited(x_240, x_3, x_4, x_5);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_unbox(x_247);
lean_dec(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
x_251 = l_Lean_Expr_fvarId_x21(x_234);
lean_dec(x_234);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_253 = l___private_Lean_Elab_Match_26__markAsVisited(x_240, x_250, x_4, x_249);
lean_dec(x_4);
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_253, 0);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_255, 0);
lean_dec(x_257);
lean_ctor_set(x_255, 0, x_252);
return x_253;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
lean_dec(x_255);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_252);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_253, 0, x_259);
return x_253;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_253, 0);
x_261 = lean_ctor_get(x_253, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_253);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_263 = x_260;
} else {
 lean_dec_ref(x_260);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_252);
lean_ctor_set(x_264, 1, x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_261);
return x_265;
}
}
else
{
uint8_t x_266; 
lean_dec(x_240);
lean_dec(x_4);
x_266 = !lean_is_exclusive(x_245);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_245, 0);
lean_dec(x_267);
x_268 = !lean_is_exclusive(x_246);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_246, 0);
lean_dec(x_269);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_234);
lean_ctor_set(x_246, 0, x_270);
return x_245;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_246, 1);
lean_inc(x_271);
lean_dec(x_246);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_234);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
lean_ctor_set(x_245, 0, x_273);
return x_245;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_274 = lean_ctor_get(x_245, 1);
lean_inc(x_274);
lean_dec(x_245);
x_275 = lean_ctor_get(x_246, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_276 = x_246;
} else {
 lean_dec_ref(x_246);
 x_276 = lean_box(0);
}
x_277 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_277, 0, x_234);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_274);
return x_279;
}
}
}
}
else
{
lean_object* x_280; 
lean_dec(x_4);
lean_dec(x_1);
x_280 = lean_box(0);
x_235 = x_280;
goto block_239;
}
block_239:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_235);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_234);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_3);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_5);
return x_238;
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_umapMAux___main___at_Lean_Elab_Term_ToDepElimPattern_main___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_toDepElimPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_NameSet_empty;
x_6 = l_Lean_Elab_Term_ToDepElimPattern_main___main(x_1, x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_14 = l_Lean_Elab_Term_toDepElimPattern(x_1, x_13, x_4, x_5);
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
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern contains metavariables ");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_Expr_hasExprMVar(x_9);
if (x_12 == 0)
{
lean_dec(x_9);
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_15 = l_Lean_indentExpr(x_14);
x_16 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_throwError___rarg(x_17, x_3, x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = 0;
x_11 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_8, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_30__elabPatterns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("patterns: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_30__elabPatterns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_30__elabPatterns___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_30__elabPatterns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_30__elabPatterns___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_30__elabPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_24__elabPatternsAux___boxed), 6, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_7);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_withSynthesize___rarg(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_4);
x_15 = l_Lean_Elab_Term_finalizePatternDecls(x_1, x_4, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = x_13;
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__1), 4, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = x_19;
lean_inc(x_4);
x_21 = lean_apply_2(x_20, x_4, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = x_22;
lean_inc(x_16);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__2), 5, 3);
lean_closure_set(x_25, 0, x_16);
lean_closure_set(x_25, 1, x_6);
lean_closure_set(x_25, 2, x_24);
lean_inc(x_4);
x_26 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3(x_22, x_6, x_4, x_23);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = x_25;
lean_inc(x_4);
x_29 = lean_apply_2(x_28, x_4, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_33 = l_Array_toList___rarg(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_10, 0, x_34);
x_35 = l_Lean_Elab_Term_getOptions(x_4, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_40 = l_Lean_checkTraceOption(x_37, x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_30);
lean_dec(x_4);
lean_ctor_set(x_35, 0, x_10);
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_35);
x_41 = x_30;
x_42 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__4(x_6, x_41);
x_43 = x_42;
x_44 = l_Lean_MessageData_ofArray(x_43);
lean_dec(x_43);
x_45 = l___private_Lean_Elab_Match_30__elabPatterns___closed__3;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_Term_logTrace(x_39, x_46, x_4, x_38);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_10);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_55 = l_Lean_checkTraceOption(x_52, x_54);
lean_dec(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_30);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = x_30;
x_58 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__4(x_6, x_57);
x_59 = x_58;
x_60 = l_Lean_MessageData_ofArray(x_59);
lean_dec(x_59);
x_61 = l___private_Lean_Elab_Match_30__elabPatterns___closed__3;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Elab_Term_logTrace(x_54, x_62, x_4, x_53);
lean_dec(x_4);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_16);
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_29);
if (x_67 == 0)
{
return x_29;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_29, 0);
x_69 = lean_ctor_get(x_29, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_29);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_25);
lean_dec(x_16);
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_26);
if (x_71 == 0)
{
return x_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_26, 0);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_16);
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_10, 0);
x_84 = lean_ctor_get(x_10, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_10);
lean_inc(x_4);
x_85 = l_Lean_Elab_Term_finalizePatternDecls(x_1, x_4, x_11);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = x_83;
x_89 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__1), 4, 2);
lean_closure_set(x_89, 0, x_6);
lean_closure_set(x_89, 1, x_88);
x_90 = x_89;
lean_inc(x_4);
x_91 = lean_apply_2(x_90, x_4, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_92);
x_94 = x_92;
lean_inc(x_86);
x_95 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__2), 5, 3);
lean_closure_set(x_95, 0, x_86);
lean_closure_set(x_95, 1, x_6);
lean_closure_set(x_95, 2, x_94);
lean_inc(x_4);
x_96 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3(x_92, x_6, x_4, x_93);
lean_dec(x_92);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = x_95;
lean_inc(x_4);
x_99 = lean_apply_2(x_98, x_4, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Array_toList___rarg(x_86);
lean_dec(x_86);
x_103 = l_Array_toList___rarg(x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_84);
x_106 = l_Lean_Elab_Term_getOptions(x_4, x_101);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_111 = l_Lean_checkTraceOption(x_107, x_110);
lean_dec(x_107);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_100);
lean_dec(x_4);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_109);
x_113 = x_100;
x_114 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__4(x_6, x_113);
x_115 = x_114;
x_116 = l_Lean_MessageData_ofArray(x_115);
lean_dec(x_115);
x_117 = l___private_Lean_Elab_Match_30__elabPatterns___closed__3;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_Elab_Term_logTrace(x_110, x_118, x_4, x_108);
lean_dec(x_4);
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
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_105);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_4);
x_123 = lean_ctor_get(x_99, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_99, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_125 = x_99;
} else {
 lean_dec_ref(x_99);
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
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_95);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_4);
x_127 = lean_ctor_get(x_96, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_96, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_129 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_4);
x_131 = lean_ctor_get(x_91, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_91, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_133 = x_91;
} else {
 lean_dec_ref(x_91);
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
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_4);
x_135 = lean_ctor_get(x_85, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_85, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_137 = x_85;
} else {
 lean_dec_ref(x_85);
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
lean_dec(x_4);
x_139 = !lean_is_exclusive(x_9);
if (x_139 == 0)
{
return x_9;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_9, 0);
x_141 = lean_ctor_get(x_9, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_9);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_30__elabPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_30__elabPatterns(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_5);
x_8 = l___private_Lean_Elab_Match_30__elabPatterns(x_4, x_7, x_2, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = 1;
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_elabTerm(x_14, x_15, x_16, x_5, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = l_List_redLength___main___rarg(x_20);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_dec(x_21);
x_23 = l_List_toArrayAux___main___rarg(x_20, x_22);
x_24 = x_23;
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__withAltsAux___main___spec__1(x_25, x_24);
x_27 = x_26;
x_28 = l_Array_isEmpty___rarg(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc(x_5);
x_29 = l_Lean_Elab_Term_mkLambda(x_27, x_18, x_5, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_30);
lean_ctor_set(x_9, 1, x_30);
x_32 = l_Lean_Elab_Term_getOptions(x_5, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_3);
x_36 = l_Lean_checkTraceOption(x_34, x_3);
lean_dec(x_34);
if (x_36 == 0)
{
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_32, 0, x_9);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_free_object(x_32);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_30);
x_38 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Term_logTrace(x_3, x_39, x_5, x_35);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_9);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
lean_inc(x_3);
x_47 = l_Lean_checkTraceOption(x_45, x_3);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_30);
x_50 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Elab_Term_logTrace(x_3, x_51, x_5, x_46);
lean_dec(x_5);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_29);
if (x_56 == 0)
{
return x_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_29, 0);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_29);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_27);
x_60 = l_Lean_mkThunk(x_18);
lean_inc(x_60);
lean_ctor_set(x_9, 1, x_60);
x_61 = l_Lean_Elab_Term_getOptions(x_5, x_19);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_3);
x_65 = l_Lean_checkTraceOption(x_63, x_3);
lean_dec(x_63);
if (x_65 == 0)
{
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_61, 0, x_9);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_free_object(x_61);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_60);
x_67 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Elab_Term_logTrace(x_3, x_68, x_5, x_64);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_9);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_9);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
lean_inc(x_3);
x_76 = l_Lean_checkTraceOption(x_74, x_3);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_9);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_60);
x_79 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_Term_logTrace(x_3, x_80, x_5, x_75);
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
lean_ctor_set(x_84, 0, x_9);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_17);
if (x_85 == 0)
{
return x_17;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_17, 0);
x_87 = lean_ctor_get(x_17, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_17);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_9, 0);
x_90 = lean_ctor_get(x_9, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_9);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
lean_dec(x_1);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_90);
x_93 = 1;
lean_inc(x_5);
x_94 = l_Lean_Elab_Term_elabTerm(x_91, x_92, x_93, x_5, x_10);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
x_98 = l_List_redLength___main___rarg(x_97);
x_99 = lean_mk_empty_array_with_capacity(x_98);
lean_dec(x_98);
x_100 = l_List_toArrayAux___main___rarg(x_97, x_99);
x_101 = x_100;
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__withAltsAux___main___spec__1(x_102, x_101);
x_104 = x_103;
x_105 = l_Array_isEmpty___rarg(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_inc(x_5);
x_106 = l_Lean_Elab_Term_mkLambda(x_104, x_95, x_5, x_96);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_89);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_Term_getOptions(x_5, x_108);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
lean_inc(x_3);
x_114 = l_Lean_checkTraceOption(x_111, x_3);
lean_dec(x_111);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_107);
x_117 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_Elab_Term_logTrace(x_3, x_118, x_5, x_112);
lean_dec(x_5);
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
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_89);
lean_dec(x_5);
lean_dec(x_3);
x_123 = lean_ctor_get(x_106, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_106, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_125 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_104);
x_127 = l_Lean_mkThunk(x_95);
lean_inc(x_127);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_89);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Term_getOptions(x_5, x_96);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
lean_inc(x_3);
x_133 = l_Lean_checkTraceOption(x_130, x_3);
lean_dec(x_130);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_127);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_132);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_127);
x_136 = l_Lean_Elab_Term_elabMatchAltView___lambda__1___closed__3;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Elab_Term_logTrace(x_3, x_137, x_5, x_131);
lean_dec(x_5);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_128);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_89);
lean_dec(x_5);
lean_dec(x_3);
x_142 = lean_ctor_get(x_94, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_94, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_144 = x_94;
} else {
 lean_dec_ref(x_94);
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
}
else
{
uint8_t x_146; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_8);
if (x_146 == 0)
{
return x_8;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_8, 0);
x_148 = lean_ctor_get(x_8, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_8);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
x_14 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed), 6, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_Elab_Term_getOptions(x_3, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_checkTraceOption(x_17, x_14);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_12, x_15, x_3, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_29 = l_Lean_Elab_Term_logTrace(x_14, x_28, x_3, x_18);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_12, x_15, x_3, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
x_38 = lean_ctor_get(x_3, 2);
x_39 = lean_ctor_get(x_3, 3);
x_40 = lean_ctor_get(x_3, 4);
x_41 = lean_ctor_get(x_3, 5);
x_42 = lean_ctor_get(x_3, 6);
x_43 = lean_ctor_get(x_3, 7);
x_44 = lean_ctor_get(x_3, 8);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_48 = lean_ctor_get(x_3, 9);
lean_inc(x_48);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_3);
x_49 = l_Lean_Elab_replaceRef(x_5, x_48);
lean_dec(x_48);
lean_dec(x_5);
x_50 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_38);
lean_ctor_set(x_50, 3, x_39);
lean_ctor_set(x_50, 4, x_40);
lean_ctor_set(x_50, 5, x_41);
lean_ctor_set(x_50, 6, x_42);
lean_ctor_set(x_50, 7, x_43);
lean_ctor_set(x_50, 8, x_44);
lean_ctor_set(x_50, 9, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*10, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 1, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 2, x_47);
lean_inc(x_50);
x_51 = l___private_Lean_Elab_Match_21__collectPatternVars(x_1, x_50, x_4);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed), 6, 3);
lean_closure_set(x_57, 0, x_55);
lean_closure_set(x_57, 1, x_2);
lean_closure_set(x_57, 2, x_56);
x_58 = l_Lean_Elab_Term_getOptions(x_50, x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_checkTraceOption(x_59, x_56);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_54, x_57, x_50, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = l_Array_toList___rarg(x_54);
x_64 = l_List_toString___at_Lean_Elab_Term_elabMatchAltView___spec__1(x_63);
x_65 = l_Array_HasRepr___rarg___closed__1;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_Elab_Term_elabMatchAltView___closed__3;
x_70 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_Elab_Term_logTrace(x_56, x_70, x_50, x_60);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l___private_Lean_Elab_Match_23__withPatternVars___rarg(x_54, x_57, x_50, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_50);
lean_dec(x_2);
x_74 = lean_ctor_get(x_51, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_51, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_76 = x_51;
} else {
 lean_dec_ref(x_51);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
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
lean_object* l_Lean_Elab_Term_elabMatchAltView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabMatchAltView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_11 = l_Lean_Meta_DepElim_mkElim(x_1, x_2, x_3, x_9, x_6);
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
x_38 = l_Lean_Meta_DepElim_mkElim(x_1, x_2, x_3, x_35, x_37);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambda), 4, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elim");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_183; 
x_183 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4);
if (lean_obj_tag(x_183) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = 0;
x_186 = lean_box(0);
lean_inc(x_3);
x_187 = l_Lean_Elab_Term_mkFreshTypeMVar(x_185, x_186, x_3, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_5 = x_188;
x_6 = x_189;
goto block_182;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_183, 1);
lean_inc(x_190);
lean_dec(x_183);
x_191 = lean_ctor_get(x_2, 0);
lean_inc(x_191);
lean_dec(x_2);
x_5 = x_191;
x_6 = x_190;
goto block_182;
}
}
else
{
uint8_t x_192; 
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_183);
if (x_192 == 0)
{
return x_183;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_183, 0);
x_194 = lean_ctor_get(x_183, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_183);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
block_182:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_10, x_9, x_11, x_12);
lean_dec(x_9);
x_14 = x_13;
x_15 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__1(x_11, x_14);
x_16 = x_15;
x_17 = lean_array_get_size(x_16);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_Match_5__elabMatchOptType(x_1, x_17, x_3, x_6);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_Match_8__getMatchAlts(x_1);
lean_inc(x_3);
x_22 = l_Lean_Elab_Term_expandMacrosInPatterns(x_21, x_3, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_19);
x_25 = l___private_Lean_Elab_Match_7__elabDiscrs(x_16, x_19, x_5, x_3, x_24);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = x_23;
lean_inc(x_19);
x_29 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__2), 5, 3);
lean_closure_set(x_29, 0, x_19);
lean_closure_set(x_29, 1, x_11);
lean_closure_set(x_29, 2, x_28);
x_30 = x_29;
lean_inc(x_3);
x_31 = lean_apply_2(x_30, x_3, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = x_32;
lean_inc(x_34);
x_35 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__3(x_11, x_34);
x_36 = x_35;
x_37 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_31__elabMatchCore___spec__4(x_11, x_34);
x_38 = x_37;
lean_inc(x_3);
lean_inc(x_19);
x_39 = l_Lean_Elab_Term_mkMotiveType(x_19, x_5, x_3, x_33);
lean_dec(x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_41, 4);
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_41, 4, x_46);
x_47 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__1;
x_48 = l_Lean_Meta_forallTelescopeReducing___rarg(x_19, x_47, x_45, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_3);
x_51 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_40, x_50, x_44);
x_52 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__3;
lean_inc(x_3);
x_53 = l_Lean_Elab_Term_mkAuxName(x_52, x_3, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Array_toList___rarg(x_38);
lean_dec(x_38);
lean_inc(x_3);
x_57 = l_Lean_Elab_Term_mkElim(x_54, x_42, x_56, x_3, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_mkApp(x_60, x_49);
x_62 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_26, x_26, x_11, x_61);
lean_dec(x_26);
x_63 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_36, x_36, x_11, x_62);
lean_dec(x_36);
x_64 = l_Lean_Elab_Term_getOptions(x_3, x_59);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
x_68 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_69 = l_Lean_checkTraceOption(x_66, x_68);
lean_dec(x_66);
if (x_69 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_free_object(x_64);
lean_inc(x_63);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_63);
x_71 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__6;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Elab_Term_logTrace(x_68, x_72, x_3, x_67);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_63);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_64, 0);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_64);
x_80 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_81 = l_Lean_checkTraceOption(x_78, x_80);
lean_dec(x_78);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_3);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_63);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_63);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_63);
x_84 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__6;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Term_logTrace(x_80, x_85, x_3, x_79);
lean_dec(x_3);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_49);
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_57);
if (x_90 == 0)
{
return x_57;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_57, 0);
x_92 = lean_ctor_get(x_57, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_57);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_49);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_53);
if (x_94 == 0)
{
return x_53;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_53, 0);
x_96 = lean_ctor_get(x_53, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_53);
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
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_26);
x_98 = !lean_is_exclusive(x_48);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_48, 0);
x_100 = lean_ctor_get(x_48, 1);
lean_inc(x_3);
x_101 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_99);
x_102 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_40, x_100, x_44);
lean_ctor_set(x_48, 1, x_102);
lean_ctor_set(x_48, 0, x_101);
return x_48;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_48, 0);
x_104 = lean_ctor_get(x_48, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_48);
lean_inc(x_3);
x_105 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_103);
x_106 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_40, x_104, x_44);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_108 = lean_ctor_get(x_41, 0);
x_109 = lean_ctor_get(x_41, 1);
x_110 = lean_ctor_get(x_41, 2);
x_111 = lean_ctor_get(x_41, 3);
x_112 = lean_ctor_get(x_41, 4);
x_113 = lean_ctor_get(x_41, 5);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_41);
x_114 = lean_ctor_get(x_3, 0);
lean_inc(x_114);
x_115 = l_Lean_TraceState_Inhabited___closed__1;
x_116 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_109);
lean_ctor_set(x_116, 2, x_110);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set(x_116, 4, x_115);
lean_ctor_set(x_116, 5, x_113);
x_117 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__1;
x_118 = l_Lean_Meta_forallTelescopeReducing___rarg(x_19, x_117, x_114, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_3);
x_121 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_40, x_120, x_112);
x_122 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__3;
lean_inc(x_3);
x_123 = l_Lean_Elab_Term_mkAuxName(x_122, x_3, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Array_toList___rarg(x_38);
lean_dec(x_38);
lean_inc(x_3);
x_127 = l_Lean_Elab_Term_mkElim(x_124, x_42, x_126, x_3, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_mkApp(x_130, x_119);
x_132 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_26, x_26, x_11, x_131);
lean_dec(x_26);
x_133 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_36, x_36, x_11, x_132);
lean_dec(x_36);
x_134 = l_Lean_Elab_Term_getOptions(x_3, x_129);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_139 = l_Lean_checkTraceOption(x_135, x_138);
lean_dec(x_135);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_3);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_137);
lean_inc(x_133);
x_141 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_141, 0, x_133);
x_142 = l___private_Lean_Elab_Match_31__elabMatchCore___closed__6;
x_143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_Elab_Term_logTrace(x_138, x_143, x_3, x_136);
lean_dec(x_3);
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
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_119);
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_3);
x_148 = lean_ctor_get(x_127, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_127, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_150 = x_127;
} else {
 lean_dec_ref(x_127);
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
lean_dec(x_119);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_3);
x_152 = lean_ctor_get(x_123, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_123, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_154 = x_123;
} else {
 lean_dec_ref(x_123);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_26);
x_156 = lean_ctor_get(x_118, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_118, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_158 = x_118;
} else {
 lean_dec_ref(x_118);
 x_158 = lean_box(0);
}
lean_inc(x_3);
x_159 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_156);
x_160 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_40, x_157, x_112);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_39);
if (x_162 == 0)
{
return x_39;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_39, 0);
x_164 = lean_ctor_get(x_39, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_39);
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
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
x_166 = !lean_is_exclusive(x_31);
if (x_166 == 0)
{
return x_31;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_31, 0);
x_168 = lean_ctor_get(x_31, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_31);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
x_170 = !lean_is_exclusive(x_25);
if (x_170 == 0)
{
return x_25;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_25, 0);
x_172 = lean_ctor_get(x_25, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_25);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
x_174 = !lean_is_exclusive(x_22);
if (x_174 == 0)
{
return x_22;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_22, 0);
x_176 = lean_ctor_get(x_22, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_22);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
x_178 = !lean_is_exclusive(x_18);
if (x_178 == 0)
{
return x_18;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_18, 0);
x_180 = lean_ctor_get(x_18, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_18);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_31__elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_31__elabMatchCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5() {
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
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6() {
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
lean_object* _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
x_2 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_20 = l___private_Lean_Elab_Match_32__mkMatchType___main(x_1, x_19, x_3, x_8);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_26 = l_Lean_Syntax_getArg(x_14, x_7);
lean_dec(x_14);
x_27 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_28 = l_Lean_addMacroScope(x_12, x_27, x_4);
x_29 = lean_box(0);
x_30 = l_Lean_SourceInfo_inhabited___closed__1;
x_31 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2;
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_nullKind___closed__2;
lean_inc(x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
x_38 = lean_array_push(x_37, x_36);
x_39 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4;
x_40 = lean_array_push(x_38, x_39);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_42 = lean_array_push(x_40, x_41);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
x_44 = lean_array_push(x_42, x_43);
x_45 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_33, x_46);
x_48 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5;
x_49 = lean_array_push(x_47, x_48);
x_50 = lean_array_push(x_33, x_26);
x_51 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6;
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_push(x_34, x_41);
x_54 = l_Lean_mkTermIdFromIdent___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_52, x_55);
x_57 = l_Lean_Parser_Term_eq___elambda__1___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_array_push(x_33, x_58);
x_60 = lean_array_push(x_59, x_48);
x_61 = lean_array_push(x_60, x_22);
x_62 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_49, x_63);
x_65 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_20, 0, x_66);
return x_20;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_67 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7;
x_68 = lean_array_push(x_67, x_22);
x_69 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_20, 0, x_70);
return x_20;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_20, 0);
x_72 = lean_ctor_get(x_20, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_20);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Syntax_getArg(x_14, x_73);
x_75 = l_Lean_Syntax_isNone(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_76 = l_Lean_Syntax_getArg(x_14, x_7);
lean_dec(x_14);
x_77 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_78 = l_Lean_addMacroScope(x_12, x_77, x_4);
x_79 = lean_box(0);
x_80 = l_Lean_SourceInfo_inhabited___closed__1;
x_81 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2;
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set(x_82, 3, x_79);
x_83 = l_Array_empty___closed__1;
x_84 = lean_array_push(x_83, x_82);
x_85 = l_Lean_nullKind___closed__2;
lean_inc(x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
x_88 = lean_array_push(x_87, x_86);
x_89 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4;
x_90 = lean_array_push(x_88, x_89);
x_91 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_92 = lean_array_push(x_90, x_91);
x_93 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
x_94 = lean_array_push(x_92, x_93);
x_95 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_array_push(x_83, x_96);
x_98 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_array_push(x_83, x_76);
x_101 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6;
x_102 = lean_array_push(x_100, x_101);
x_103 = lean_array_push(x_84, x_91);
x_104 = l_Lean_mkTermIdFromIdent___closed__2;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_array_push(x_102, x_105);
x_107 = l_Lean_Parser_Term_eq___elambda__1___closed__2;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_83, x_108);
x_110 = lean_array_push(x_109, x_98);
x_111 = lean_array_push(x_110, x_71);
x_112 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_array_push(x_99, x_113);
x_115 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_72);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_118 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7;
x_119 = lean_array_push(x_118, x_71);
x_120 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_72);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_123 = lean_ctor_get(x_3, 0);
x_124 = lean_ctor_get(x_3, 2);
x_125 = lean_ctor_get(x_3, 3);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_123);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_4);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_125);
x_127 = lean_array_fget(x_1, x_2);
x_128 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_inc(x_127);
x_129 = l_Lean_Syntax_isOfKind(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_4);
x_130 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_2 = x_130;
x_3 = x_126;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_132 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_133 = l___private_Lean_Elab_Match_32__mkMatchType___main(x_1, x_132, x_126, x_8);
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
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Lean_Syntax_getArg(x_127, x_137);
x_139 = l_Lean_Syntax_isNone(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_140 = l_Lean_Syntax_getArg(x_127, x_7);
lean_dec(x_127);
x_141 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_142 = l_Lean_addMacroScope(x_123, x_141, x_4);
x_143 = lean_box(0);
x_144 = l_Lean_SourceInfo_inhabited___closed__1;
x_145 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2;
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_142);
lean_ctor_set(x_146, 3, x_143);
x_147 = l_Array_empty___closed__1;
x_148 = lean_array_push(x_147, x_146);
x_149 = l_Lean_nullKind___closed__2;
lean_inc(x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
x_152 = lean_array_push(x_151, x_150);
x_153 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4;
x_154 = lean_array_push(x_152, x_153);
x_155 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_156 = lean_array_push(x_154, x_155);
x_157 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
x_158 = lean_array_push(x_156, x_157);
x_159 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_array_push(x_147, x_160);
x_162 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5;
x_163 = lean_array_push(x_161, x_162);
x_164 = lean_array_push(x_147, x_140);
x_165 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6;
x_166 = lean_array_push(x_164, x_165);
x_167 = lean_array_push(x_148, x_155);
x_168 = l_Lean_mkTermIdFromIdent___closed__2;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
x_170 = lean_array_push(x_166, x_169);
x_171 = l_Lean_Parser_Term_eq___elambda__1___closed__2;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = lean_array_push(x_147, x_172);
x_174 = lean_array_push(x_173, x_162);
x_175 = lean_array_push(x_174, x_134);
x_176 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = lean_array_push(x_163, x_177);
x_179 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
if (lean_is_scalar(x_136)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_136;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_135);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_4);
x_182 = l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7;
x_183 = lean_array_push(x_182, x_134);
x_184 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
if (lean_is_scalar(x_136)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_136;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_135);
return x_186;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_32__mkMatchType___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_32__mkMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_32__mkMatchType___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_32__mkMatchType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_32__mkMatchType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_33__mkOptType(lean_object* x_1) {
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
lean_object* _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq.refl");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__4() {
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
lean_object* _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__9;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
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
x_30 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__3;
x_31 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__5;
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Lean_mkTermIdFromIdent___closed__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_push(x_33, x_38);
x_40 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
x_41 = lean_array_push(x_39, x_40);
x_42 = l_Lean_mkAppStx___closed__8;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__6;
x_45 = lean_array_push(x_44, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_push(x_24, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_2, x_48);
lean_dec(x_2);
x_2 = x_49;
x_3 = x_47;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_2, x_51);
lean_dec(x_2);
x_53 = lean_array_push(x_3, x_9);
x_2 = x_52;
x_3 = x_53;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Match_34__mkNewDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_34__mkNewDiscrs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Match_35__mkNewPatterns___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid number of patterns, expected #");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_15 = l___private_Lean_Elab_Match_35__mkNewPatterns___main___closed__1;
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_19);
x_29 = lean_array_push(x_5, x_19);
x_30 = l_List_reprAux___main___rarg___closed__1;
x_31 = l_Lean_mkAtomFrom(x_19, x_30);
lean_dec(x_19);
x_32 = lean_array_push(x_29, x_31);
x_33 = l_Lean_Syntax_getArg(x_27, x_26);
lean_dec(x_27);
x_34 = l_Lean_mkTermIdFromIdent(x_33);
x_35 = lean_array_push(x_32, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_4, x_36);
lean_dec(x_4);
x_4 = x_37;
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_4, x_39);
lean_dec(x_4);
x_41 = lean_array_push(x_5, x_19);
x_4 = x_40;
x_5 = x_41;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_35__mkNewPatterns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_35__mkNewPatterns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_35__mkNewPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Match_35__mkNewPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Match_36__mkNewAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = l_Array_empty___closed__1;
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Match_35__mkNewPatterns___main(x_2, x_1, x_7, x_5, x_8, x_3, x_4);
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
lean_object* l___private_Lean_Elab_Match_36__mkNewAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_36__mkNewAlt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_37__mkNewAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_37__mkNewAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_37__mkNewAlts___spec__2(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Match_37__mkNewAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_36__mkNewAlt___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_37__mkNewAlts___spec__1(x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_37__mkNewAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_LeanInit_14__mapSepElemsMAux___main___at___private_Lean_Elab_Match_37__mkNewAlts___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Match_37__mkNewAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mapSepElemsM___at___private_Lean_Elab_Match_37__mkNewAlts___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_37__mkNewAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_37__mkNewAlts(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match expected type should not be provided when discriminants with equality proofs are used");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___spec__1(x_1, x_10, x_11, x_8);
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
x_17 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___closed__1;
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
x_20 = l___private_Lean_Elab_Match_32__mkMatchType___main(x_6, x_8, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_copyInfo(x_21, x_1);
x_24 = l___private_Lean_Elab_Match_33__mkOptType(x_23);
x_25 = l_Lean_Syntax_setArg(x_1, x_7, x_24);
lean_inc(x_2);
x_26 = l___private_Lean_Elab_Match_34__mkNewDiscrs___main(x_6, x_8, x_9, x_2, x_22);
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
x_35 = l___private_Lean_Elab_Match_37__mkNewAlts(x_6, x_34, x_2, x_28);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* x_5; lean_object* x_6; uint8_t x_34; lean_object* x_1763; uint8_t x_1764; 
x_1763 = l_Lean_Parser_Term_match___elambda__1___closed__1;
lean_inc(x_1);
x_1764 = l_Lean_Syntax_isOfKind(x_1, x_1763);
if (x_1764 == 0)
{
uint8_t x_1765; 
x_1765 = 0;
x_34 = x_1765;
goto block_1762;
}
else
{
lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; uint8_t x_1769; 
x_1766 = l_Lean_Syntax_getArgs(x_1);
x_1767 = lean_array_get_size(x_1766);
lean_dec(x_1766);
x_1768 = lean_unsigned_to_nat(6u);
x_1769 = lean_nat_dec_eq(x_1767, x_1768);
lean_dec(x_1767);
x_34 = x_1769;
goto block_1762;
}
block_33:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Match_31__elabMatchCore(x_1, x_2, x_3, x_6);
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
block_1762:
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
x_52 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_51, x_46);
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
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_1756; uint8_t x_1757; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = l_Lean_Syntax_getArg(x_1, x_80);
x_1756 = l_Lean_nullKind___closed__2;
lean_inc(x_81);
x_1757 = l_Lean_Syntax_isOfKind(x_81, x_1756);
if (x_1757 == 0)
{
uint8_t x_1758; 
x_1758 = 0;
x_82 = x_1758;
goto block_1755;
}
else
{
lean_object* x_1759; lean_object* x_1760; uint8_t x_1761; 
x_1759 = l_Lean_Syntax_getArgs(x_81);
x_1760 = lean_array_get_size(x_1759);
lean_dec(x_1759);
x_1761 = lean_nat_dec_eq(x_1760, x_80);
lean_dec(x_1760);
x_82 = x_1761;
goto block_1755;
}
block_1755:
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
x_100 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_99, x_94);
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
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_1748; uint8_t x_1749; 
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Lean_Syntax_getArg(x_81, x_128);
lean_dec(x_81);
x_1748 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_inc(x_129);
x_1749 = l_Lean_Syntax_isOfKind(x_129, x_1748);
if (x_1749 == 0)
{
uint8_t x_1750; 
x_1750 = 0;
x_130 = x_1750;
goto block_1747;
}
else
{
lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; uint8_t x_1754; 
x_1751 = l_Lean_Syntax_getArgs(x_129);
x_1752 = lean_array_get_size(x_1751);
lean_dec(x_1751);
x_1753 = lean_unsigned_to_nat(2u);
x_1754 = lean_nat_dec_eq(x_1752, x_1753);
lean_dec(x_1752);
x_130 = x_1754;
goto block_1747;
}
block_1747:
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
x_148 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_147, x_142);
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
lean_object* x_176; uint8_t x_177; lean_object* x_1741; uint8_t x_1742; 
x_176 = l_Lean_Syntax_getArg(x_129, x_128);
x_1741 = l_Lean_nullKind___closed__2;
lean_inc(x_176);
x_1742 = l_Lean_Syntax_isOfKind(x_176, x_1741);
if (x_1742 == 0)
{
uint8_t x_1743; 
lean_dec(x_176);
x_1743 = 0;
x_177 = x_1743;
goto block_1740;
}
else
{
lean_object* x_1744; lean_object* x_1745; uint8_t x_1746; 
x_1744 = l_Lean_Syntax_getArgs(x_176);
lean_dec(x_176);
x_1745 = lean_array_get_size(x_1744);
lean_dec(x_1744);
x_1746 = lean_nat_dec_eq(x_1745, x_128);
lean_dec(x_1745);
x_177 = x_1746;
goto block_1740;
}
block_1740:
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
x_195 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_194, x_189);
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
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_1030; uint8_t x_1031; uint8_t x_1032; 
x_223 = l_Lean_Syntax_getArg(x_129, x_80);
lean_dec(x_129);
x_224 = lean_unsigned_to_nat(2u);
x_225 = l_Lean_Syntax_getArg(x_1, x_224);
x_1030 = l_Lean_nullKind___closed__2;
lean_inc(x_225);
x_1031 = l_Lean_Syntax_isOfKind(x_225, x_1030);
if (x_1031 == 0)
{
uint8_t x_1736; 
x_1736 = 0;
x_1032 = x_1736;
goto block_1735;
}
else
{
lean_object* x_1737; lean_object* x_1738; uint8_t x_1739; 
x_1737 = l_Lean_Syntax_getArgs(x_225);
x_1738 = lean_array_get_size(x_1737);
lean_dec(x_1737);
x_1739 = lean_nat_dec_eq(x_1738, x_128);
lean_dec(x_1738);
x_1032 = x_1739;
goto block_1735;
}
block_1029:
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
x_244 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_243, x_238);
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
lean_object* x_272; uint8_t x_273; lean_object* x_1023; uint8_t x_1024; 
x_272 = l_Lean_Syntax_getArg(x_225, x_128);
lean_dec(x_225);
x_1023 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_272);
x_1024 = l_Lean_Syntax_isOfKind(x_272, x_1023);
if (x_1024 == 0)
{
uint8_t x_1025; 
x_1025 = 0;
x_273 = x_1025;
goto block_1022;
}
else
{
lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; 
x_1026 = l_Lean_Syntax_getArgs(x_272);
x_1027 = lean_array_get_size(x_1026);
lean_dec(x_1026);
x_1028 = lean_nat_dec_eq(x_1027, x_224);
lean_dec(x_1027);
x_273 = x_1028;
goto block_1022;
}
block_1022:
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
x_291 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_290, x_285);
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
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_691; uint8_t x_692; uint8_t x_693; 
x_319 = l_Lean_Syntax_getArg(x_272, x_80);
lean_dec(x_272);
x_320 = lean_unsigned_to_nat(4u);
x_321 = l_Lean_Syntax_getArg(x_1, x_320);
x_691 = l_Lean_nullKind___closed__2;
lean_inc(x_321);
x_692 = l_Lean_Syntax_isOfKind(x_321, x_691);
if (x_692 == 0)
{
uint8_t x_1018; 
x_1018 = 0;
x_693 = x_1018;
goto block_1017;
}
else
{
lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; 
x_1019 = l_Lean_Syntax_getArgs(x_321);
x_1020 = lean_array_get_size(x_1019);
lean_dec(x_1019);
x_1021 = lean_nat_dec_eq(x_1020, x_128);
lean_dec(x_1020);
x_693 = x_1021;
goto block_1017;
}
block_690:
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
x_340 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_339, x_334);
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
lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_684; uint8_t x_685; 
x_368 = lean_unsigned_to_nat(5u);
x_369 = l_Lean_Syntax_getArg(x_1, x_368);
x_684 = l_Lean_nullKind___closed__2;
lean_inc(x_369);
x_685 = l_Lean_Syntax_isOfKind(x_369, x_684);
if (x_685 == 0)
{
uint8_t x_686; 
x_686 = 0;
x_370 = x_686;
goto block_683;
}
else
{
lean_object* x_687; lean_object* x_688; uint8_t x_689; 
x_687 = l_Lean_Syntax_getArgs(x_369);
x_688 = lean_array_get_size(x_687);
lean_dec(x_687);
x_689 = lean_nat_dec_eq(x_688, x_80);
lean_dec(x_688);
x_370 = x_689;
goto block_683;
}
block_683:
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
x_388 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_387, x_382);
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
lean_object* x_416; uint8_t x_417; lean_object* x_676; uint8_t x_677; 
x_416 = l_Lean_Syntax_getArg(x_369, x_128);
lean_dec(x_369);
x_676 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_416);
x_677 = l_Lean_Syntax_isOfKind(x_416, x_676);
if (x_677 == 0)
{
uint8_t x_678; 
x_678 = 0;
x_417 = x_678;
goto block_675;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_679 = l_Lean_Syntax_getArgs(x_416);
x_680 = lean_array_get_size(x_679);
lean_dec(x_679);
x_681 = lean_unsigned_to_nat(3u);
x_682 = lean_nat_dec_eq(x_680, x_681);
lean_dec(x_680);
x_417 = x_682;
goto block_675;
}
block_675:
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
x_435 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_434, x_429);
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
lean_object* x_463; uint8_t x_464; lean_object* x_669; uint8_t x_670; 
x_463 = l_Lean_Syntax_getArg(x_416, x_128);
x_669 = l_Lean_nullKind___closed__2;
lean_inc(x_463);
x_670 = l_Lean_Syntax_isOfKind(x_463, x_669);
if (x_670 == 0)
{
uint8_t x_671; 
x_671 = 0;
x_464 = x_671;
goto block_668;
}
else
{
lean_object* x_672; lean_object* x_673; uint8_t x_674; 
x_672 = l_Lean_Syntax_getArgs(x_463);
x_673 = lean_array_get_size(x_672);
lean_dec(x_672);
x_674 = lean_nat_dec_eq(x_673, x_80);
lean_dec(x_673);
x_464 = x_674;
goto block_668;
}
block_668:
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
x_482 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_481, x_476);
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
lean_object* x_510; uint8_t x_511; lean_object* x_662; uint8_t x_663; 
x_510 = l_Lean_Syntax_getArg(x_463, x_128);
lean_dec(x_463);
x_662 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_510);
x_663 = l_Lean_Syntax_isOfKind(x_510, x_662);
if (x_663 == 0)
{
uint8_t x_664; 
x_664 = 0;
x_511 = x_664;
goto block_661;
}
else
{
lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_665 = l_Lean_Syntax_getArgs(x_510);
x_666 = lean_array_get_size(x_665);
lean_dec(x_665);
x_667 = lean_nat_dec_eq(x_666, x_224);
lean_dec(x_666);
x_511 = x_667;
goto block_661;
}
block_661:
{
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_510);
lean_dec(x_416);
lean_dec(x_319);
lean_dec(x_223);
x_512 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = l_Lean_Elab_Term_getEnv___rarg(x_514);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 0);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
x_520 = lean_ctor_get(x_516, 2);
lean_inc(x_520);
x_521 = lean_ctor_get(x_516, 3);
lean_inc(x_521);
x_522 = lean_ctor_get(x_516, 4);
lean_inc(x_522);
x_523 = lean_ctor_get(x_516, 5);
lean_inc(x_523);
x_524 = lean_ctor_get(x_3, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_524, 3);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 4);
lean_inc(x_526);
lean_dec(x_524);
x_527 = lean_environment_main_module(x_517);
x_528 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_513);
lean_ctor_set(x_528, 2, x_525);
lean_ctor_set(x_528, 3, x_526);
lean_inc(x_1);
x_529 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_528, x_523);
if (lean_obj_tag(x_529) == 0)
{
uint8_t x_530; 
x_530 = !lean_is_exclusive(x_516);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_531 = lean_ctor_get(x_516, 5);
lean_dec(x_531);
x_532 = lean_ctor_get(x_516, 4);
lean_dec(x_532);
x_533 = lean_ctor_get(x_516, 3);
lean_dec(x_533);
x_534 = lean_ctor_get(x_516, 2);
lean_dec(x_534);
x_535 = lean_ctor_get(x_516, 1);
lean_dec(x_535);
x_536 = lean_ctor_get(x_516, 0);
lean_dec(x_536);
x_537 = lean_ctor_get(x_529, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_529, 1);
lean_inc(x_538);
lean_dec(x_529);
lean_ctor_set(x_516, 5, x_538);
x_5 = x_537;
x_6 = x_516;
goto block_33;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_516);
x_539 = lean_ctor_get(x_529, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_529, 1);
lean_inc(x_540);
lean_dec(x_529);
x_541 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_541, 0, x_518);
lean_ctor_set(x_541, 1, x_519);
lean_ctor_set(x_541, 2, x_520);
lean_ctor_set(x_541, 3, x_521);
lean_ctor_set(x_541, 4, x_522);
lean_ctor_set(x_541, 5, x_540);
x_5 = x_539;
x_6 = x_541;
goto block_33;
}
}
else
{
lean_object* x_542; 
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_2);
lean_dec(x_1);
x_542 = lean_ctor_get(x_529, 0);
lean_inc(x_542);
lean_dec(x_529);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_545, 0, x_544);
x_546 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_546, 0, x_545);
x_547 = l_Lean_Elab_Term_throwErrorAt___rarg(x_543, x_546, x_3, x_516);
lean_dec(x_543);
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
else
{
lean_object* x_552; uint8_t x_553; 
lean_dec(x_3);
x_552 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_516);
x_553 = !lean_is_exclusive(x_552);
if (x_553 == 0)
{
return x_552;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_552, 0);
x_555 = lean_ctor_get(x_552, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_552);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
return x_556;
}
}
}
}
else
{
lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_557 = l_Lean_Syntax_getArg(x_510, x_128);
x_558 = l_Lean_identKind___closed__2;
lean_inc(x_557);
x_559 = l_Lean_Syntax_isOfKind(x_557, x_558);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_557);
lean_dec(x_510);
lean_dec(x_416);
lean_dec(x_319);
lean_dec(x_223);
x_560 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_563 = l_Lean_Elab_Term_getEnv___rarg(x_562);
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
x_565 = lean_ctor_get(x_563, 0);
lean_inc(x_565);
lean_dec(x_563);
x_566 = lean_ctor_get(x_564, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_564, 1);
lean_inc(x_567);
x_568 = lean_ctor_get(x_564, 2);
lean_inc(x_568);
x_569 = lean_ctor_get(x_564, 3);
lean_inc(x_569);
x_570 = lean_ctor_get(x_564, 4);
lean_inc(x_570);
x_571 = lean_ctor_get(x_564, 5);
lean_inc(x_571);
x_572 = lean_ctor_get(x_3, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_572, 3);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 4);
lean_inc(x_574);
lean_dec(x_572);
x_575 = lean_environment_main_module(x_565);
x_576 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_561);
lean_ctor_set(x_576, 2, x_573);
lean_ctor_set(x_576, 3, x_574);
lean_inc(x_1);
x_577 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_576, x_571);
if (lean_obj_tag(x_577) == 0)
{
uint8_t x_578; 
x_578 = !lean_is_exclusive(x_564);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_579 = lean_ctor_get(x_564, 5);
lean_dec(x_579);
x_580 = lean_ctor_get(x_564, 4);
lean_dec(x_580);
x_581 = lean_ctor_get(x_564, 3);
lean_dec(x_581);
x_582 = lean_ctor_get(x_564, 2);
lean_dec(x_582);
x_583 = lean_ctor_get(x_564, 1);
lean_dec(x_583);
x_584 = lean_ctor_get(x_564, 0);
lean_dec(x_584);
x_585 = lean_ctor_get(x_577, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_577, 1);
lean_inc(x_586);
lean_dec(x_577);
lean_ctor_set(x_564, 5, x_586);
x_5 = x_585;
x_6 = x_564;
goto block_33;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_564);
x_587 = lean_ctor_get(x_577, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_577, 1);
lean_inc(x_588);
lean_dec(x_577);
x_589 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_589, 0, x_566);
lean_ctor_set(x_589, 1, x_567);
lean_ctor_set(x_589, 2, x_568);
lean_ctor_set(x_589, 3, x_569);
lean_ctor_set(x_589, 4, x_570);
lean_ctor_set(x_589, 5, x_588);
x_5 = x_587;
x_6 = x_589;
goto block_33;
}
}
else
{
lean_object* x_590; 
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_2);
lean_dec(x_1);
x_590 = lean_ctor_get(x_577, 0);
lean_inc(x_590);
lean_dec(x_577);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_593, 0, x_592);
x_594 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_594, 0, x_593);
x_595 = l_Lean_Elab_Term_throwErrorAt___rarg(x_591, x_594, x_3, x_564);
lean_dec(x_591);
x_596 = !lean_is_exclusive(x_595);
if (x_596 == 0)
{
return x_595;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_595, 0);
x_598 = lean_ctor_get(x_595, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_595);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
else
{
lean_object* x_600; uint8_t x_601; 
lean_dec(x_3);
x_600 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_564);
x_601 = !lean_is_exclusive(x_600);
if (x_601 == 0)
{
return x_600;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_600, 0);
x_603 = lean_ctor_get(x_600, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_600);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
}
else
{
lean_object* x_605; uint8_t x_606; lean_object* x_655; uint8_t x_656; 
x_605 = l_Lean_Syntax_getArg(x_510, x_80);
lean_dec(x_510);
x_655 = l_Lean_nullKind___closed__2;
lean_inc(x_605);
x_656 = l_Lean_Syntax_isOfKind(x_605, x_655);
if (x_656 == 0)
{
uint8_t x_657; 
lean_dec(x_605);
x_657 = 0;
x_606 = x_657;
goto block_654;
}
else
{
lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_658 = l_Lean_Syntax_getArgs(x_605);
lean_dec(x_605);
x_659 = lean_array_get_size(x_658);
lean_dec(x_658);
x_660 = lean_nat_dec_eq(x_659, x_128);
lean_dec(x_659);
x_606 = x_660;
goto block_654;
}
block_654:
{
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_557);
lean_dec(x_416);
lean_dec(x_319);
lean_dec(x_223);
x_607 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = l_Lean_Elab_Term_getEnv___rarg(x_609);
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 0);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_ctor_get(x_611, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_611, 2);
lean_inc(x_615);
x_616 = lean_ctor_get(x_611, 3);
lean_inc(x_616);
x_617 = lean_ctor_get(x_611, 4);
lean_inc(x_617);
x_618 = lean_ctor_get(x_611, 5);
lean_inc(x_618);
x_619 = lean_ctor_get(x_3, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_619, 3);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 4);
lean_inc(x_621);
lean_dec(x_619);
x_622 = lean_environment_main_module(x_612);
x_623 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_608);
lean_ctor_set(x_623, 2, x_620);
lean_ctor_set(x_623, 3, x_621);
lean_inc(x_1);
x_624 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_623, x_618);
if (lean_obj_tag(x_624) == 0)
{
uint8_t x_625; 
x_625 = !lean_is_exclusive(x_611);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_626 = lean_ctor_get(x_611, 5);
lean_dec(x_626);
x_627 = lean_ctor_get(x_611, 4);
lean_dec(x_627);
x_628 = lean_ctor_get(x_611, 3);
lean_dec(x_628);
x_629 = lean_ctor_get(x_611, 2);
lean_dec(x_629);
x_630 = lean_ctor_get(x_611, 1);
lean_dec(x_630);
x_631 = lean_ctor_get(x_611, 0);
lean_dec(x_631);
x_632 = lean_ctor_get(x_624, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_624, 1);
lean_inc(x_633);
lean_dec(x_624);
lean_ctor_set(x_611, 5, x_633);
x_5 = x_632;
x_6 = x_611;
goto block_33;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_611);
x_634 = lean_ctor_get(x_624, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_624, 1);
lean_inc(x_635);
lean_dec(x_624);
x_636 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_636, 0, x_613);
lean_ctor_set(x_636, 1, x_614);
lean_ctor_set(x_636, 2, x_615);
lean_ctor_set(x_636, 3, x_616);
lean_ctor_set(x_636, 4, x_617);
lean_ctor_set(x_636, 5, x_635);
x_5 = x_634;
x_6 = x_636;
goto block_33;
}
}
else
{
lean_object* x_637; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_2);
lean_dec(x_1);
x_637 = lean_ctor_get(x_624, 0);
lean_inc(x_637);
lean_dec(x_624);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_640, 0, x_639);
x_641 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_641, 0, x_640);
x_642 = l_Lean_Elab_Term_throwErrorAt___rarg(x_638, x_641, x_3, x_611);
lean_dec(x_638);
x_643 = !lean_is_exclusive(x_642);
if (x_643 == 0)
{
return x_642;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_642, 0);
x_645 = lean_ctor_get(x_642, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_642);
x_646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
return x_646;
}
}
else
{
lean_object* x_647; uint8_t x_648; 
lean_dec(x_3);
x_647 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_611);
x_648 = !lean_is_exclusive(x_647);
if (x_648 == 0)
{
return x_647;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_647, 0);
x_650 = lean_ctor_get(x_647, 1);
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_647);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
return x_651;
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = l_Lean_Syntax_getArg(x_416, x_224);
lean_dec(x_416);
x_653 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_223, x_557, x_319, x_652, x_2, x_3, x_4);
return x_653;
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
block_1017:
{
if (x_693 == 0)
{
if (x_692 == 0)
{
uint8_t x_694; 
lean_dec(x_321);
x_694 = 0;
x_322 = x_694;
goto block_690;
}
else
{
lean_object* x_695; lean_object* x_696; uint8_t x_697; 
x_695 = l_Lean_Syntax_getArgs(x_321);
lean_dec(x_321);
x_696 = lean_array_get_size(x_695);
lean_dec(x_695);
x_697 = lean_nat_dec_eq(x_696, x_80);
lean_dec(x_696);
x_322 = x_697;
goto block_690;
}
}
else
{
lean_object* x_698; lean_object* x_699; uint8_t x_700; uint8_t x_1012; 
lean_dec(x_321);
x_698 = lean_unsigned_to_nat(5u);
x_699 = l_Lean_Syntax_getArg(x_1, x_698);
lean_inc(x_699);
x_1012 = l_Lean_Syntax_isOfKind(x_699, x_691);
if (x_1012 == 0)
{
uint8_t x_1013; 
x_1013 = 0;
x_700 = x_1013;
goto block_1011;
}
else
{
lean_object* x_1014; lean_object* x_1015; uint8_t x_1016; 
x_1014 = l_Lean_Syntax_getArgs(x_699);
x_1015 = lean_array_get_size(x_1014);
lean_dec(x_1014);
x_1016 = lean_nat_dec_eq(x_1015, x_80);
lean_dec(x_1015);
x_700 = x_1016;
goto block_1011;
}
block_1011:
{
if (x_700 == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_699);
lean_dec(x_319);
lean_dec(x_223);
x_701 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
x_704 = l_Lean_Elab_Term_getEnv___rarg(x_703);
x_705 = lean_ctor_get(x_704, 1);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 0);
lean_inc(x_706);
lean_dec(x_704);
x_707 = lean_ctor_get(x_705, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_705, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_705, 2);
lean_inc(x_709);
x_710 = lean_ctor_get(x_705, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_705, 4);
lean_inc(x_711);
x_712 = lean_ctor_get(x_705, 5);
lean_inc(x_712);
x_713 = lean_ctor_get(x_3, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_713, 3);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 4);
lean_inc(x_715);
lean_dec(x_713);
x_716 = lean_environment_main_module(x_706);
x_717 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_702);
lean_ctor_set(x_717, 2, x_714);
lean_ctor_set(x_717, 3, x_715);
lean_inc(x_1);
x_718 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_717, x_712);
if (lean_obj_tag(x_718) == 0)
{
uint8_t x_719; 
x_719 = !lean_is_exclusive(x_705);
if (x_719 == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_720 = lean_ctor_get(x_705, 5);
lean_dec(x_720);
x_721 = lean_ctor_get(x_705, 4);
lean_dec(x_721);
x_722 = lean_ctor_get(x_705, 3);
lean_dec(x_722);
x_723 = lean_ctor_get(x_705, 2);
lean_dec(x_723);
x_724 = lean_ctor_get(x_705, 1);
lean_dec(x_724);
x_725 = lean_ctor_get(x_705, 0);
lean_dec(x_725);
x_726 = lean_ctor_get(x_718, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_718, 1);
lean_inc(x_727);
lean_dec(x_718);
lean_ctor_set(x_705, 5, x_727);
x_5 = x_726;
x_6 = x_705;
goto block_33;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_705);
x_728 = lean_ctor_get(x_718, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_718, 1);
lean_inc(x_729);
lean_dec(x_718);
x_730 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_730, 0, x_707);
lean_ctor_set(x_730, 1, x_708);
lean_ctor_set(x_730, 2, x_709);
lean_ctor_set(x_730, 3, x_710);
lean_ctor_set(x_730, 4, x_711);
lean_ctor_set(x_730, 5, x_729);
x_5 = x_728;
x_6 = x_730;
goto block_33;
}
}
else
{
lean_object* x_731; 
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
lean_dec(x_708);
lean_dec(x_707);
lean_dec(x_2);
lean_dec(x_1);
x_731 = lean_ctor_get(x_718, 0);
lean_inc(x_731);
lean_dec(x_718);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
x_734 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_734, 0, x_733);
x_735 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_735, 0, x_734);
x_736 = l_Lean_Elab_Term_throwErrorAt___rarg(x_732, x_735, x_3, x_705);
lean_dec(x_732);
x_737 = !lean_is_exclusive(x_736);
if (x_737 == 0)
{
return x_736;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_736, 0);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_736);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
else
{
lean_object* x_741; uint8_t x_742; 
lean_dec(x_3);
x_741 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_705);
x_742 = !lean_is_exclusive(x_741);
if (x_742 == 0)
{
return x_741;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_741, 0);
x_744 = lean_ctor_get(x_741, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_741);
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_744);
return x_745;
}
}
}
}
else
{
lean_object* x_746; uint8_t x_747; lean_object* x_1004; uint8_t x_1005; 
x_746 = l_Lean_Syntax_getArg(x_699, x_128);
lean_dec(x_699);
x_1004 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_746);
x_1005 = l_Lean_Syntax_isOfKind(x_746, x_1004);
if (x_1005 == 0)
{
uint8_t x_1006; 
x_1006 = 0;
x_747 = x_1006;
goto block_1003;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; 
x_1007 = l_Lean_Syntax_getArgs(x_746);
x_1008 = lean_array_get_size(x_1007);
lean_dec(x_1007);
x_1009 = lean_unsigned_to_nat(3u);
x_1010 = lean_nat_dec_eq(x_1008, x_1009);
lean_dec(x_1008);
x_747 = x_1010;
goto block_1003;
}
block_1003:
{
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_746);
lean_dec(x_319);
lean_dec(x_223);
x_748 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec(x_748);
x_751 = l_Lean_Elab_Term_getEnv___rarg(x_750);
x_752 = lean_ctor_get(x_751, 1);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 0);
lean_inc(x_753);
lean_dec(x_751);
x_754 = lean_ctor_get(x_752, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
x_756 = lean_ctor_get(x_752, 2);
lean_inc(x_756);
x_757 = lean_ctor_get(x_752, 3);
lean_inc(x_757);
x_758 = lean_ctor_get(x_752, 4);
lean_inc(x_758);
x_759 = lean_ctor_get(x_752, 5);
lean_inc(x_759);
x_760 = lean_ctor_get(x_3, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_760, 3);
lean_inc(x_761);
x_762 = lean_ctor_get(x_760, 4);
lean_inc(x_762);
lean_dec(x_760);
x_763 = lean_environment_main_module(x_753);
x_764 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_749);
lean_ctor_set(x_764, 2, x_761);
lean_ctor_set(x_764, 3, x_762);
lean_inc(x_1);
x_765 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_764, x_759);
if (lean_obj_tag(x_765) == 0)
{
uint8_t x_766; 
x_766 = !lean_is_exclusive(x_752);
if (x_766 == 0)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_767 = lean_ctor_get(x_752, 5);
lean_dec(x_767);
x_768 = lean_ctor_get(x_752, 4);
lean_dec(x_768);
x_769 = lean_ctor_get(x_752, 3);
lean_dec(x_769);
x_770 = lean_ctor_get(x_752, 2);
lean_dec(x_770);
x_771 = lean_ctor_get(x_752, 1);
lean_dec(x_771);
x_772 = lean_ctor_get(x_752, 0);
lean_dec(x_772);
x_773 = lean_ctor_get(x_765, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_765, 1);
lean_inc(x_774);
lean_dec(x_765);
lean_ctor_set(x_752, 5, x_774);
x_5 = x_773;
x_6 = x_752;
goto block_33;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_752);
x_775 = lean_ctor_get(x_765, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_765, 1);
lean_inc(x_776);
lean_dec(x_765);
x_777 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_777, 0, x_754);
lean_ctor_set(x_777, 1, x_755);
lean_ctor_set(x_777, 2, x_756);
lean_ctor_set(x_777, 3, x_757);
lean_ctor_set(x_777, 4, x_758);
lean_ctor_set(x_777, 5, x_776);
x_5 = x_775;
x_6 = x_777;
goto block_33;
}
}
else
{
lean_object* x_778; 
lean_dec(x_758);
lean_dec(x_757);
lean_dec(x_756);
lean_dec(x_755);
lean_dec(x_754);
lean_dec(x_2);
lean_dec(x_1);
x_778 = lean_ctor_get(x_765, 0);
lean_inc(x_778);
lean_dec(x_765);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; 
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
x_781 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_781, 0, x_780);
x_782 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_782, 0, x_781);
x_783 = l_Lean_Elab_Term_throwErrorAt___rarg(x_779, x_782, x_3, x_752);
lean_dec(x_779);
x_784 = !lean_is_exclusive(x_783);
if (x_784 == 0)
{
return x_783;
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_783, 0);
x_786 = lean_ctor_get(x_783, 1);
lean_inc(x_786);
lean_inc(x_785);
lean_dec(x_783);
x_787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_787, 0, x_785);
lean_ctor_set(x_787, 1, x_786);
return x_787;
}
}
else
{
lean_object* x_788; uint8_t x_789; 
lean_dec(x_3);
x_788 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_752);
x_789 = !lean_is_exclusive(x_788);
if (x_789 == 0)
{
return x_788;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_788, 0);
x_791 = lean_ctor_get(x_788, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_788);
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
lean_object* x_793; uint8_t x_794; uint8_t x_998; 
x_793 = l_Lean_Syntax_getArg(x_746, x_128);
lean_inc(x_793);
x_998 = l_Lean_Syntax_isOfKind(x_793, x_691);
if (x_998 == 0)
{
uint8_t x_999; 
x_999 = 0;
x_794 = x_999;
goto block_997;
}
else
{
lean_object* x_1000; lean_object* x_1001; uint8_t x_1002; 
x_1000 = l_Lean_Syntax_getArgs(x_793);
x_1001 = lean_array_get_size(x_1000);
lean_dec(x_1000);
x_1002 = lean_nat_dec_eq(x_1001, x_80);
lean_dec(x_1001);
x_794 = x_1002;
goto block_997;
}
block_997:
{
if (x_794 == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_793);
lean_dec(x_746);
lean_dec(x_319);
lean_dec(x_223);
x_795 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = l_Lean_Elab_Term_getEnv___rarg(x_797);
x_799 = lean_ctor_get(x_798, 1);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 0);
lean_inc(x_800);
lean_dec(x_798);
x_801 = lean_ctor_get(x_799, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_799, 1);
lean_inc(x_802);
x_803 = lean_ctor_get(x_799, 2);
lean_inc(x_803);
x_804 = lean_ctor_get(x_799, 3);
lean_inc(x_804);
x_805 = lean_ctor_get(x_799, 4);
lean_inc(x_805);
x_806 = lean_ctor_get(x_799, 5);
lean_inc(x_806);
x_807 = lean_ctor_get(x_3, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_807, 3);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 4);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_environment_main_module(x_800);
x_811 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_796);
lean_ctor_set(x_811, 2, x_808);
lean_ctor_set(x_811, 3, x_809);
lean_inc(x_1);
x_812 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_811, x_806);
if (lean_obj_tag(x_812) == 0)
{
uint8_t x_813; 
x_813 = !lean_is_exclusive(x_799);
if (x_813 == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_814 = lean_ctor_get(x_799, 5);
lean_dec(x_814);
x_815 = lean_ctor_get(x_799, 4);
lean_dec(x_815);
x_816 = lean_ctor_get(x_799, 3);
lean_dec(x_816);
x_817 = lean_ctor_get(x_799, 2);
lean_dec(x_817);
x_818 = lean_ctor_get(x_799, 1);
lean_dec(x_818);
x_819 = lean_ctor_get(x_799, 0);
lean_dec(x_819);
x_820 = lean_ctor_get(x_812, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_812, 1);
lean_inc(x_821);
lean_dec(x_812);
lean_ctor_set(x_799, 5, x_821);
x_5 = x_820;
x_6 = x_799;
goto block_33;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_799);
x_822 = lean_ctor_get(x_812, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_812, 1);
lean_inc(x_823);
lean_dec(x_812);
x_824 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_824, 0, x_801);
lean_ctor_set(x_824, 1, x_802);
lean_ctor_set(x_824, 2, x_803);
lean_ctor_set(x_824, 3, x_804);
lean_ctor_set(x_824, 4, x_805);
lean_ctor_set(x_824, 5, x_823);
x_5 = x_822;
x_6 = x_824;
goto block_33;
}
}
else
{
lean_object* x_825; 
lean_dec(x_805);
lean_dec(x_804);
lean_dec(x_803);
lean_dec(x_802);
lean_dec(x_801);
lean_dec(x_2);
lean_dec(x_1);
x_825 = lean_ctor_get(x_812, 0);
lean_inc(x_825);
lean_dec(x_812);
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
x_830 = l_Lean_Elab_Term_throwErrorAt___rarg(x_826, x_829, x_3, x_799);
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
lean_dec(x_3);
x_835 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_799);
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
lean_object* x_840; uint8_t x_841; lean_object* x_991; uint8_t x_992; 
x_840 = l_Lean_Syntax_getArg(x_793, x_128);
lean_dec(x_793);
x_991 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_840);
x_992 = l_Lean_Syntax_isOfKind(x_840, x_991);
if (x_992 == 0)
{
uint8_t x_993; 
x_993 = 0;
x_841 = x_993;
goto block_990;
}
else
{
lean_object* x_994; lean_object* x_995; uint8_t x_996; 
x_994 = l_Lean_Syntax_getArgs(x_840);
x_995 = lean_array_get_size(x_994);
lean_dec(x_994);
x_996 = lean_nat_dec_eq(x_995, x_224);
lean_dec(x_995);
x_841 = x_996;
goto block_990;
}
block_990:
{
if (x_841 == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_840);
lean_dec(x_746);
lean_dec(x_319);
lean_dec(x_223);
x_842 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_842, 1);
lean_inc(x_844);
lean_dec(x_842);
x_845 = l_Lean_Elab_Term_getEnv___rarg(x_844);
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 0);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_846, 1);
lean_inc(x_849);
x_850 = lean_ctor_get(x_846, 2);
lean_inc(x_850);
x_851 = lean_ctor_get(x_846, 3);
lean_inc(x_851);
x_852 = lean_ctor_get(x_846, 4);
lean_inc(x_852);
x_853 = lean_ctor_get(x_846, 5);
lean_inc(x_853);
x_854 = lean_ctor_get(x_3, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_854, 3);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 4);
lean_inc(x_856);
lean_dec(x_854);
x_857 = lean_environment_main_module(x_847);
x_858 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_843);
lean_ctor_set(x_858, 2, x_855);
lean_ctor_set(x_858, 3, x_856);
lean_inc(x_1);
x_859 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_858, x_853);
if (lean_obj_tag(x_859) == 0)
{
uint8_t x_860; 
x_860 = !lean_is_exclusive(x_846);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_861 = lean_ctor_get(x_846, 5);
lean_dec(x_861);
x_862 = lean_ctor_get(x_846, 4);
lean_dec(x_862);
x_863 = lean_ctor_get(x_846, 3);
lean_dec(x_863);
x_864 = lean_ctor_get(x_846, 2);
lean_dec(x_864);
x_865 = lean_ctor_get(x_846, 1);
lean_dec(x_865);
x_866 = lean_ctor_get(x_846, 0);
lean_dec(x_866);
x_867 = lean_ctor_get(x_859, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_859, 1);
lean_inc(x_868);
lean_dec(x_859);
lean_ctor_set(x_846, 5, x_868);
x_5 = x_867;
x_6 = x_846;
goto block_33;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_846);
x_869 = lean_ctor_get(x_859, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_859, 1);
lean_inc(x_870);
lean_dec(x_859);
x_871 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_871, 0, x_848);
lean_ctor_set(x_871, 1, x_849);
lean_ctor_set(x_871, 2, x_850);
lean_ctor_set(x_871, 3, x_851);
lean_ctor_set(x_871, 4, x_852);
lean_ctor_set(x_871, 5, x_870);
x_5 = x_869;
x_6 = x_871;
goto block_33;
}
}
else
{
lean_object* x_872; 
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_2);
lean_dec(x_1);
x_872 = lean_ctor_get(x_859, 0);
lean_inc(x_872);
lean_dec(x_859);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; uint8_t x_878; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_875, 0, x_874);
x_876 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_876, 0, x_875);
x_877 = l_Lean_Elab_Term_throwErrorAt___rarg(x_873, x_876, x_3, x_846);
lean_dec(x_873);
x_878 = !lean_is_exclusive(x_877);
if (x_878 == 0)
{
return x_877;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_877, 0);
x_880 = lean_ctor_get(x_877, 1);
lean_inc(x_880);
lean_inc(x_879);
lean_dec(x_877);
x_881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_880);
return x_881;
}
}
else
{
lean_object* x_882; uint8_t x_883; 
lean_dec(x_3);
x_882 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_846);
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
}
}
else
{
lean_object* x_887; lean_object* x_888; uint8_t x_889; 
x_887 = l_Lean_Syntax_getArg(x_840, x_128);
x_888 = l_Lean_identKind___closed__2;
lean_inc(x_887);
x_889 = l_Lean_Syntax_isOfKind(x_887, x_888);
if (x_889 == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_887);
lean_dec(x_840);
lean_dec(x_746);
lean_dec(x_319);
lean_dec(x_223);
x_890 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = l_Lean_Elab_Term_getEnv___rarg(x_892);
x_894 = lean_ctor_get(x_893, 1);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 0);
lean_inc(x_895);
lean_dec(x_893);
x_896 = lean_ctor_get(x_894, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_894, 1);
lean_inc(x_897);
x_898 = lean_ctor_get(x_894, 2);
lean_inc(x_898);
x_899 = lean_ctor_get(x_894, 3);
lean_inc(x_899);
x_900 = lean_ctor_get(x_894, 4);
lean_inc(x_900);
x_901 = lean_ctor_get(x_894, 5);
lean_inc(x_901);
x_902 = lean_ctor_get(x_3, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_902, 3);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 4);
lean_inc(x_904);
lean_dec(x_902);
x_905 = lean_environment_main_module(x_895);
x_906 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_891);
lean_ctor_set(x_906, 2, x_903);
lean_ctor_set(x_906, 3, x_904);
lean_inc(x_1);
x_907 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_906, x_901);
if (lean_obj_tag(x_907) == 0)
{
uint8_t x_908; 
x_908 = !lean_is_exclusive(x_894);
if (x_908 == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_909 = lean_ctor_get(x_894, 5);
lean_dec(x_909);
x_910 = lean_ctor_get(x_894, 4);
lean_dec(x_910);
x_911 = lean_ctor_get(x_894, 3);
lean_dec(x_911);
x_912 = lean_ctor_get(x_894, 2);
lean_dec(x_912);
x_913 = lean_ctor_get(x_894, 1);
lean_dec(x_913);
x_914 = lean_ctor_get(x_894, 0);
lean_dec(x_914);
x_915 = lean_ctor_get(x_907, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_907, 1);
lean_inc(x_916);
lean_dec(x_907);
lean_ctor_set(x_894, 5, x_916);
x_5 = x_915;
x_6 = x_894;
goto block_33;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
lean_dec(x_894);
x_917 = lean_ctor_get(x_907, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_907, 1);
lean_inc(x_918);
lean_dec(x_907);
x_919 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_919, 0, x_896);
lean_ctor_set(x_919, 1, x_897);
lean_ctor_set(x_919, 2, x_898);
lean_ctor_set(x_919, 3, x_899);
lean_ctor_set(x_919, 4, x_900);
lean_ctor_set(x_919, 5, x_918);
x_5 = x_917;
x_6 = x_919;
goto block_33;
}
}
else
{
lean_object* x_920; 
lean_dec(x_900);
lean_dec(x_899);
lean_dec(x_898);
lean_dec(x_897);
lean_dec(x_896);
lean_dec(x_2);
lean_dec(x_1);
x_920 = lean_ctor_get(x_907, 0);
lean_inc(x_920);
lean_dec(x_907);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; uint8_t x_926; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
lean_dec(x_920);
x_923 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_923, 0, x_922);
x_924 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_924, 0, x_923);
x_925 = l_Lean_Elab_Term_throwErrorAt___rarg(x_921, x_924, x_3, x_894);
lean_dec(x_921);
x_926 = !lean_is_exclusive(x_925);
if (x_926 == 0)
{
return x_925;
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_927 = lean_ctor_get(x_925, 0);
x_928 = lean_ctor_get(x_925, 1);
lean_inc(x_928);
lean_inc(x_927);
lean_dec(x_925);
x_929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_929, 0, x_927);
lean_ctor_set(x_929, 1, x_928);
return x_929;
}
}
else
{
lean_object* x_930; uint8_t x_931; 
lean_dec(x_3);
x_930 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_894);
x_931 = !lean_is_exclusive(x_930);
if (x_931 == 0)
{
return x_930;
}
else
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_932 = lean_ctor_get(x_930, 0);
x_933 = lean_ctor_get(x_930, 1);
lean_inc(x_933);
lean_inc(x_932);
lean_dec(x_930);
x_934 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_934, 0, x_932);
lean_ctor_set(x_934, 1, x_933);
return x_934;
}
}
}
}
else
{
lean_object* x_935; uint8_t x_936; uint8_t x_985; 
x_935 = l_Lean_Syntax_getArg(x_840, x_80);
lean_dec(x_840);
lean_inc(x_935);
x_985 = l_Lean_Syntax_isOfKind(x_935, x_691);
if (x_985 == 0)
{
uint8_t x_986; 
lean_dec(x_935);
x_986 = 0;
x_936 = x_986;
goto block_984;
}
else
{
lean_object* x_987; lean_object* x_988; uint8_t x_989; 
x_987 = l_Lean_Syntax_getArgs(x_935);
lean_dec(x_935);
x_988 = lean_array_get_size(x_987);
lean_dec(x_987);
x_989 = lean_nat_dec_eq(x_988, x_128);
lean_dec(x_988);
x_936 = x_989;
goto block_984;
}
block_984:
{
if (x_936 == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_887);
lean_dec(x_746);
lean_dec(x_319);
lean_dec(x_223);
x_937 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_937, 1);
lean_inc(x_939);
lean_dec(x_937);
x_940 = l_Lean_Elab_Term_getEnv___rarg(x_939);
x_941 = lean_ctor_get(x_940, 1);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 0);
lean_inc(x_942);
lean_dec(x_940);
x_943 = lean_ctor_get(x_941, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
x_945 = lean_ctor_get(x_941, 2);
lean_inc(x_945);
x_946 = lean_ctor_get(x_941, 3);
lean_inc(x_946);
x_947 = lean_ctor_get(x_941, 4);
lean_inc(x_947);
x_948 = lean_ctor_get(x_941, 5);
lean_inc(x_948);
x_949 = lean_ctor_get(x_3, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_949, 3);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 4);
lean_inc(x_951);
lean_dec(x_949);
x_952 = lean_environment_main_module(x_942);
x_953 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_938);
lean_ctor_set(x_953, 2, x_950);
lean_ctor_set(x_953, 3, x_951);
lean_inc(x_1);
x_954 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_953, x_948);
if (lean_obj_tag(x_954) == 0)
{
uint8_t x_955; 
x_955 = !lean_is_exclusive(x_941);
if (x_955 == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_956 = lean_ctor_get(x_941, 5);
lean_dec(x_956);
x_957 = lean_ctor_get(x_941, 4);
lean_dec(x_957);
x_958 = lean_ctor_get(x_941, 3);
lean_dec(x_958);
x_959 = lean_ctor_get(x_941, 2);
lean_dec(x_959);
x_960 = lean_ctor_get(x_941, 1);
lean_dec(x_960);
x_961 = lean_ctor_get(x_941, 0);
lean_dec(x_961);
x_962 = lean_ctor_get(x_954, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_954, 1);
lean_inc(x_963);
lean_dec(x_954);
lean_ctor_set(x_941, 5, x_963);
x_5 = x_962;
x_6 = x_941;
goto block_33;
}
else
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_941);
x_964 = lean_ctor_get(x_954, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_954, 1);
lean_inc(x_965);
lean_dec(x_954);
x_966 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_966, 0, x_943);
lean_ctor_set(x_966, 1, x_944);
lean_ctor_set(x_966, 2, x_945);
lean_ctor_set(x_966, 3, x_946);
lean_ctor_set(x_966, 4, x_947);
lean_ctor_set(x_966, 5, x_965);
x_5 = x_964;
x_6 = x_966;
goto block_33;
}
}
else
{
lean_object* x_967; 
lean_dec(x_947);
lean_dec(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_943);
lean_dec(x_2);
lean_dec(x_1);
x_967 = lean_ctor_get(x_954, 0);
lean_inc(x_967);
lean_dec(x_954);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; 
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
lean_dec(x_967);
x_970 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_970, 0, x_969);
x_971 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_971, 0, x_970);
x_972 = l_Lean_Elab_Term_throwErrorAt___rarg(x_968, x_971, x_3, x_941);
lean_dec(x_968);
x_973 = !lean_is_exclusive(x_972);
if (x_973 == 0)
{
return x_972;
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_974 = lean_ctor_get(x_972, 0);
x_975 = lean_ctor_get(x_972, 1);
lean_inc(x_975);
lean_inc(x_974);
lean_dec(x_972);
x_976 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_976, 0, x_974);
lean_ctor_set(x_976, 1, x_975);
return x_976;
}
}
else
{
lean_object* x_977; uint8_t x_978; 
lean_dec(x_3);
x_977 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_941);
x_978 = !lean_is_exclusive(x_977);
if (x_978 == 0)
{
return x_977;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_ctor_get(x_977, 0);
x_980 = lean_ctor_get(x_977, 1);
lean_inc(x_980);
lean_inc(x_979);
lean_dec(x_977);
x_981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_981, 0, x_979);
lean_ctor_set(x_981, 1, x_980);
return x_981;
}
}
}
}
else
{
lean_object* x_982; lean_object* x_983; 
x_982 = l_Lean_Syntax_getArg(x_746, x_224);
lean_dec(x_746);
x_983 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_223, x_887, x_319, x_982, x_2, x_3, x_4);
return x_983;
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
block_1735:
{
if (x_1032 == 0)
{
if (x_1031 == 0)
{
uint8_t x_1033; 
x_1033 = 0;
x_226 = x_1033;
goto block_1029;
}
else
{
lean_object* x_1034; lean_object* x_1035; uint8_t x_1036; 
x_1034 = l_Lean_Syntax_getArgs(x_225);
x_1035 = lean_array_get_size(x_1034);
lean_dec(x_1034);
x_1036 = lean_nat_dec_eq(x_1035, x_80);
lean_dec(x_1035);
x_226 = x_1036;
goto block_1029;
}
}
else
{
lean_object* x_1037; lean_object* x_1038; uint8_t x_1039; uint8_t x_1405; uint8_t x_1406; 
lean_dec(x_225);
x_1037 = lean_unsigned_to_nat(4u);
x_1038 = l_Lean_Syntax_getArg(x_1, x_1037);
lean_inc(x_1038);
x_1405 = l_Lean_Syntax_isOfKind(x_1038, x_1030);
if (x_1405 == 0)
{
uint8_t x_1731; 
x_1731 = 0;
x_1406 = x_1731;
goto block_1730;
}
else
{
lean_object* x_1732; lean_object* x_1733; uint8_t x_1734; 
x_1732 = l_Lean_Syntax_getArgs(x_1038);
x_1733 = lean_array_get_size(x_1732);
lean_dec(x_1732);
x_1734 = lean_nat_dec_eq(x_1733, x_128);
lean_dec(x_1733);
x_1406 = x_1734;
goto block_1730;
}
block_1404:
{
if (x_1039 == 0)
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_223);
x_1040 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
x_1043 = l_Lean_Elab_Term_getEnv___rarg(x_1042);
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1043, 0);
lean_inc(x_1045);
lean_dec(x_1043);
x_1046 = lean_ctor_get(x_1044, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1044, 1);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1044, 2);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1044, 3);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1044, 4);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1044, 5);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_3, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1052, 3);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 4);
lean_inc(x_1054);
lean_dec(x_1052);
x_1055 = lean_environment_main_module(x_1045);
x_1056 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1041);
lean_ctor_set(x_1056, 2, x_1053);
lean_ctor_set(x_1056, 3, x_1054);
lean_inc(x_1);
x_1057 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1056, x_1051);
if (lean_obj_tag(x_1057) == 0)
{
uint8_t x_1058; 
x_1058 = !lean_is_exclusive(x_1044);
if (x_1058 == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1059 = lean_ctor_get(x_1044, 5);
lean_dec(x_1059);
x_1060 = lean_ctor_get(x_1044, 4);
lean_dec(x_1060);
x_1061 = lean_ctor_get(x_1044, 3);
lean_dec(x_1061);
x_1062 = lean_ctor_get(x_1044, 2);
lean_dec(x_1062);
x_1063 = lean_ctor_get(x_1044, 1);
lean_dec(x_1063);
x_1064 = lean_ctor_get(x_1044, 0);
lean_dec(x_1064);
x_1065 = lean_ctor_get(x_1057, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1057, 1);
lean_inc(x_1066);
lean_dec(x_1057);
lean_ctor_set(x_1044, 5, x_1066);
x_5 = x_1065;
x_6 = x_1044;
goto block_33;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_1044);
x_1067 = lean_ctor_get(x_1057, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1057, 1);
lean_inc(x_1068);
lean_dec(x_1057);
x_1069 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1069, 0, x_1046);
lean_ctor_set(x_1069, 1, x_1047);
lean_ctor_set(x_1069, 2, x_1048);
lean_ctor_set(x_1069, 3, x_1049);
lean_ctor_set(x_1069, 4, x_1050);
lean_ctor_set(x_1069, 5, x_1068);
x_5 = x_1067;
x_6 = x_1069;
goto block_33;
}
}
else
{
lean_object* x_1070; 
lean_dec(x_1050);
lean_dec(x_1049);
lean_dec(x_1048);
lean_dec(x_1047);
lean_dec(x_1046);
lean_dec(x_2);
lean_dec(x_1);
x_1070 = lean_ctor_get(x_1057, 0);
lean_inc(x_1070);
lean_dec(x_1057);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1076; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
lean_dec(x_1070);
x_1073 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1073, 0, x_1072);
x_1074 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1074, 0, x_1073);
x_1075 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1071, x_1074, x_3, x_1044);
lean_dec(x_1071);
x_1076 = !lean_is_exclusive(x_1075);
if (x_1076 == 0)
{
return x_1075;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1077 = lean_ctor_get(x_1075, 0);
x_1078 = lean_ctor_get(x_1075, 1);
lean_inc(x_1078);
lean_inc(x_1077);
lean_dec(x_1075);
x_1079 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
return x_1079;
}
}
else
{
lean_object* x_1080; uint8_t x_1081; 
lean_dec(x_3);
x_1080 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1044);
x_1081 = !lean_is_exclusive(x_1080);
if (x_1081 == 0)
{
return x_1080;
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1082 = lean_ctor_get(x_1080, 0);
x_1083 = lean_ctor_get(x_1080, 1);
lean_inc(x_1083);
lean_inc(x_1082);
lean_dec(x_1080);
x_1084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1084, 0, x_1082);
lean_ctor_set(x_1084, 1, x_1083);
return x_1084;
}
}
}
}
else
{
lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; uint8_t x_1399; 
x_1085 = lean_unsigned_to_nat(5u);
x_1086 = l_Lean_Syntax_getArg(x_1, x_1085);
lean_inc(x_1086);
x_1399 = l_Lean_Syntax_isOfKind(x_1086, x_1030);
if (x_1399 == 0)
{
uint8_t x_1400; 
x_1400 = 0;
x_1087 = x_1400;
goto block_1398;
}
else
{
lean_object* x_1401; lean_object* x_1402; uint8_t x_1403; 
x_1401 = l_Lean_Syntax_getArgs(x_1086);
x_1402 = lean_array_get_size(x_1401);
lean_dec(x_1401);
x_1403 = lean_nat_dec_eq(x_1402, x_80);
lean_dec(x_1402);
x_1087 = x_1403;
goto block_1398;
}
block_1398:
{
if (x_1087 == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1086);
lean_dec(x_223);
x_1088 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
lean_dec(x_1088);
x_1091 = l_Lean_Elab_Term_getEnv___rarg(x_1090);
x_1092 = lean_ctor_get(x_1091, 1);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1091, 0);
lean_inc(x_1093);
lean_dec(x_1091);
x_1094 = lean_ctor_get(x_1092, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1092, 1);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1092, 2);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1092, 3);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1092, 4);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1092, 5);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_3, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1100, 3);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 4);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = lean_environment_main_module(x_1093);
x_1104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1104, 0, x_1103);
lean_ctor_set(x_1104, 1, x_1089);
lean_ctor_set(x_1104, 2, x_1101);
lean_ctor_set(x_1104, 3, x_1102);
lean_inc(x_1);
x_1105 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1104, x_1099);
if (lean_obj_tag(x_1105) == 0)
{
uint8_t x_1106; 
x_1106 = !lean_is_exclusive(x_1092);
if (x_1106 == 0)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1107 = lean_ctor_get(x_1092, 5);
lean_dec(x_1107);
x_1108 = lean_ctor_get(x_1092, 4);
lean_dec(x_1108);
x_1109 = lean_ctor_get(x_1092, 3);
lean_dec(x_1109);
x_1110 = lean_ctor_get(x_1092, 2);
lean_dec(x_1110);
x_1111 = lean_ctor_get(x_1092, 1);
lean_dec(x_1111);
x_1112 = lean_ctor_get(x_1092, 0);
lean_dec(x_1112);
x_1113 = lean_ctor_get(x_1105, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1105, 1);
lean_inc(x_1114);
lean_dec(x_1105);
lean_ctor_set(x_1092, 5, x_1114);
x_5 = x_1113;
x_6 = x_1092;
goto block_33;
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1092);
x_1115 = lean_ctor_get(x_1105, 0);
lean_inc(x_1115);
x_1116 = lean_ctor_get(x_1105, 1);
lean_inc(x_1116);
lean_dec(x_1105);
x_1117 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1117, 0, x_1094);
lean_ctor_set(x_1117, 1, x_1095);
lean_ctor_set(x_1117, 2, x_1096);
lean_ctor_set(x_1117, 3, x_1097);
lean_ctor_set(x_1117, 4, x_1098);
lean_ctor_set(x_1117, 5, x_1116);
x_5 = x_1115;
x_6 = x_1117;
goto block_33;
}
}
else
{
lean_object* x_1118; 
lean_dec(x_1098);
lean_dec(x_1097);
lean_dec(x_1096);
lean_dec(x_1095);
lean_dec(x_1094);
lean_dec(x_2);
lean_dec(x_1);
x_1118 = lean_ctor_get(x_1105, 0);
lean_inc(x_1118);
lean_dec(x_1105);
if (lean_obj_tag(x_1118) == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; uint8_t x_1124; 
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1118, 1);
lean_inc(x_1120);
lean_dec(x_1118);
x_1121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1121, 0, x_1120);
x_1122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1122, 0, x_1121);
x_1123 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1119, x_1122, x_3, x_1092);
lean_dec(x_1119);
x_1124 = !lean_is_exclusive(x_1123);
if (x_1124 == 0)
{
return x_1123;
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1125 = lean_ctor_get(x_1123, 0);
x_1126 = lean_ctor_get(x_1123, 1);
lean_inc(x_1126);
lean_inc(x_1125);
lean_dec(x_1123);
x_1127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1127, 0, x_1125);
lean_ctor_set(x_1127, 1, x_1126);
return x_1127;
}
}
else
{
lean_object* x_1128; uint8_t x_1129; 
lean_dec(x_3);
x_1128 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1092);
x_1129 = !lean_is_exclusive(x_1128);
if (x_1129 == 0)
{
return x_1128;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1128, 0);
x_1131 = lean_ctor_get(x_1128, 1);
lean_inc(x_1131);
lean_inc(x_1130);
lean_dec(x_1128);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
}
}
else
{
lean_object* x_1133; uint8_t x_1134; lean_object* x_1391; uint8_t x_1392; 
x_1133 = l_Lean_Syntax_getArg(x_1086, x_128);
lean_dec(x_1086);
x_1391 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_1133);
x_1392 = l_Lean_Syntax_isOfKind(x_1133, x_1391);
if (x_1392 == 0)
{
uint8_t x_1393; 
x_1393 = 0;
x_1134 = x_1393;
goto block_1390;
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; uint8_t x_1397; 
x_1394 = l_Lean_Syntax_getArgs(x_1133);
x_1395 = lean_array_get_size(x_1394);
lean_dec(x_1394);
x_1396 = lean_unsigned_to_nat(3u);
x_1397 = lean_nat_dec_eq(x_1395, x_1396);
lean_dec(x_1395);
x_1134 = x_1397;
goto block_1390;
}
block_1390:
{
if (x_1134 == 0)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_1133);
lean_dec(x_223);
x_1135 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
x_1137 = lean_ctor_get(x_1135, 1);
lean_inc(x_1137);
lean_dec(x_1135);
x_1138 = l_Lean_Elab_Term_getEnv___rarg(x_1137);
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1138, 0);
lean_inc(x_1140);
lean_dec(x_1138);
x_1141 = lean_ctor_get(x_1139, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1139, 1);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1139, 2);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1139, 3);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1139, 4);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1139, 5);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_3, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1147, 3);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 4);
lean_inc(x_1149);
lean_dec(x_1147);
x_1150 = lean_environment_main_module(x_1140);
x_1151 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1151, 0, x_1150);
lean_ctor_set(x_1151, 1, x_1136);
lean_ctor_set(x_1151, 2, x_1148);
lean_ctor_set(x_1151, 3, x_1149);
lean_inc(x_1);
x_1152 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1151, x_1146);
if (lean_obj_tag(x_1152) == 0)
{
uint8_t x_1153; 
x_1153 = !lean_is_exclusive(x_1139);
if (x_1153 == 0)
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1154 = lean_ctor_get(x_1139, 5);
lean_dec(x_1154);
x_1155 = lean_ctor_get(x_1139, 4);
lean_dec(x_1155);
x_1156 = lean_ctor_get(x_1139, 3);
lean_dec(x_1156);
x_1157 = lean_ctor_get(x_1139, 2);
lean_dec(x_1157);
x_1158 = lean_ctor_get(x_1139, 1);
lean_dec(x_1158);
x_1159 = lean_ctor_get(x_1139, 0);
lean_dec(x_1159);
x_1160 = lean_ctor_get(x_1152, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1152, 1);
lean_inc(x_1161);
lean_dec(x_1152);
lean_ctor_set(x_1139, 5, x_1161);
x_5 = x_1160;
x_6 = x_1139;
goto block_33;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1139);
x_1162 = lean_ctor_get(x_1152, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1152, 1);
lean_inc(x_1163);
lean_dec(x_1152);
x_1164 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1164, 0, x_1141);
lean_ctor_set(x_1164, 1, x_1142);
lean_ctor_set(x_1164, 2, x_1143);
lean_ctor_set(x_1164, 3, x_1144);
lean_ctor_set(x_1164, 4, x_1145);
lean_ctor_set(x_1164, 5, x_1163);
x_5 = x_1162;
x_6 = x_1164;
goto block_33;
}
}
else
{
lean_object* x_1165; 
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec(x_1141);
lean_dec(x_2);
lean_dec(x_1);
x_1165 = lean_ctor_get(x_1152, 0);
lean_inc(x_1165);
lean_dec(x_1152);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; uint8_t x_1171; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1168, 0, x_1167);
x_1169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1169, 0, x_1168);
x_1170 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1166, x_1169, x_3, x_1139);
lean_dec(x_1166);
x_1171 = !lean_is_exclusive(x_1170);
if (x_1171 == 0)
{
return x_1170;
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1172 = lean_ctor_get(x_1170, 0);
x_1173 = lean_ctor_get(x_1170, 1);
lean_inc(x_1173);
lean_inc(x_1172);
lean_dec(x_1170);
x_1174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1174, 0, x_1172);
lean_ctor_set(x_1174, 1, x_1173);
return x_1174;
}
}
else
{
lean_object* x_1175; uint8_t x_1176; 
lean_dec(x_3);
x_1175 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1139);
x_1176 = !lean_is_exclusive(x_1175);
if (x_1176 == 0)
{
return x_1175;
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1177 = lean_ctor_get(x_1175, 0);
x_1178 = lean_ctor_get(x_1175, 1);
lean_inc(x_1178);
lean_inc(x_1177);
lean_dec(x_1175);
x_1179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1179, 0, x_1177);
lean_ctor_set(x_1179, 1, x_1178);
return x_1179;
}
}
}
}
else
{
lean_object* x_1180; uint8_t x_1181; uint8_t x_1385; 
x_1180 = l_Lean_Syntax_getArg(x_1133, x_128);
lean_inc(x_1180);
x_1385 = l_Lean_Syntax_isOfKind(x_1180, x_1030);
if (x_1385 == 0)
{
uint8_t x_1386; 
x_1386 = 0;
x_1181 = x_1386;
goto block_1384;
}
else
{
lean_object* x_1387; lean_object* x_1388; uint8_t x_1389; 
x_1387 = l_Lean_Syntax_getArgs(x_1180);
x_1388 = lean_array_get_size(x_1387);
lean_dec(x_1387);
x_1389 = lean_nat_dec_eq(x_1388, x_80);
lean_dec(x_1388);
x_1181 = x_1389;
goto block_1384;
}
block_1384:
{
if (x_1181 == 0)
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1180);
lean_dec(x_1133);
lean_dec(x_223);
x_1182 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1185 = l_Lean_Elab_Term_getEnv___rarg(x_1184);
x_1186 = lean_ctor_get(x_1185, 1);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1185, 0);
lean_inc(x_1187);
lean_dec(x_1185);
x_1188 = lean_ctor_get(x_1186, 0);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_1186, 1);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1186, 2);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1186, 3);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1186, 4);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1186, 5);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_3, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1194, 3);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1194, 4);
lean_inc(x_1196);
lean_dec(x_1194);
x_1197 = lean_environment_main_module(x_1187);
x_1198 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1198, 0, x_1197);
lean_ctor_set(x_1198, 1, x_1183);
lean_ctor_set(x_1198, 2, x_1195);
lean_ctor_set(x_1198, 3, x_1196);
lean_inc(x_1);
x_1199 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1198, x_1193);
if (lean_obj_tag(x_1199) == 0)
{
uint8_t x_1200; 
x_1200 = !lean_is_exclusive(x_1186);
if (x_1200 == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1201 = lean_ctor_get(x_1186, 5);
lean_dec(x_1201);
x_1202 = lean_ctor_get(x_1186, 4);
lean_dec(x_1202);
x_1203 = lean_ctor_get(x_1186, 3);
lean_dec(x_1203);
x_1204 = lean_ctor_get(x_1186, 2);
lean_dec(x_1204);
x_1205 = lean_ctor_get(x_1186, 1);
lean_dec(x_1205);
x_1206 = lean_ctor_get(x_1186, 0);
lean_dec(x_1206);
x_1207 = lean_ctor_get(x_1199, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1199, 1);
lean_inc(x_1208);
lean_dec(x_1199);
lean_ctor_set(x_1186, 5, x_1208);
x_5 = x_1207;
x_6 = x_1186;
goto block_33;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
lean_dec(x_1186);
x_1209 = lean_ctor_get(x_1199, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1199, 1);
lean_inc(x_1210);
lean_dec(x_1199);
x_1211 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1211, 0, x_1188);
lean_ctor_set(x_1211, 1, x_1189);
lean_ctor_set(x_1211, 2, x_1190);
lean_ctor_set(x_1211, 3, x_1191);
lean_ctor_set(x_1211, 4, x_1192);
lean_ctor_set(x_1211, 5, x_1210);
x_5 = x_1209;
x_6 = x_1211;
goto block_33;
}
}
else
{
lean_object* x_1212; 
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1189);
lean_dec(x_1188);
lean_dec(x_2);
lean_dec(x_1);
x_1212 = lean_ctor_get(x_1199, 0);
lean_inc(x_1212);
lean_dec(x_1199);
if (lean_obj_tag(x_1212) == 0)
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; uint8_t x_1218; 
x_1213 = lean_ctor_get(x_1212, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1212, 1);
lean_inc(x_1214);
lean_dec(x_1212);
x_1215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1215, 0, x_1214);
x_1216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1216, 0, x_1215);
x_1217 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1213, x_1216, x_3, x_1186);
lean_dec(x_1213);
x_1218 = !lean_is_exclusive(x_1217);
if (x_1218 == 0)
{
return x_1217;
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
x_1219 = lean_ctor_get(x_1217, 0);
x_1220 = lean_ctor_get(x_1217, 1);
lean_inc(x_1220);
lean_inc(x_1219);
lean_dec(x_1217);
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1219);
lean_ctor_set(x_1221, 1, x_1220);
return x_1221;
}
}
else
{
lean_object* x_1222; uint8_t x_1223; 
lean_dec(x_3);
x_1222 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1186);
x_1223 = !lean_is_exclusive(x_1222);
if (x_1223 == 0)
{
return x_1222;
}
else
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1224 = lean_ctor_get(x_1222, 0);
x_1225 = lean_ctor_get(x_1222, 1);
lean_inc(x_1225);
lean_inc(x_1224);
lean_dec(x_1222);
x_1226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1226, 0, x_1224);
lean_ctor_set(x_1226, 1, x_1225);
return x_1226;
}
}
}
}
else
{
lean_object* x_1227; uint8_t x_1228; lean_object* x_1378; uint8_t x_1379; 
x_1227 = l_Lean_Syntax_getArg(x_1180, x_128);
lean_dec(x_1180);
x_1378 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_1227);
x_1379 = l_Lean_Syntax_isOfKind(x_1227, x_1378);
if (x_1379 == 0)
{
uint8_t x_1380; 
x_1380 = 0;
x_1228 = x_1380;
goto block_1377;
}
else
{
lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; 
x_1381 = l_Lean_Syntax_getArgs(x_1227);
x_1382 = lean_array_get_size(x_1381);
lean_dec(x_1381);
x_1383 = lean_nat_dec_eq(x_1382, x_224);
lean_dec(x_1382);
x_1228 = x_1383;
goto block_1377;
}
block_1377:
{
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
lean_dec(x_1227);
lean_dec(x_1133);
lean_dec(x_223);
x_1229 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1229, 1);
lean_inc(x_1231);
lean_dec(x_1229);
x_1232 = l_Lean_Elab_Term_getEnv___rarg(x_1231);
x_1233 = lean_ctor_get(x_1232, 1);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1232, 0);
lean_inc(x_1234);
lean_dec(x_1232);
x_1235 = lean_ctor_get(x_1233, 0);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1233, 1);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1233, 2);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1233, 3);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1233, 4);
lean_inc(x_1239);
x_1240 = lean_ctor_get(x_1233, 5);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_3, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1241, 3);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1241, 4);
lean_inc(x_1243);
lean_dec(x_1241);
x_1244 = lean_environment_main_module(x_1234);
x_1245 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1245, 0, x_1244);
lean_ctor_set(x_1245, 1, x_1230);
lean_ctor_set(x_1245, 2, x_1242);
lean_ctor_set(x_1245, 3, x_1243);
lean_inc(x_1);
x_1246 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1245, x_1240);
if (lean_obj_tag(x_1246) == 0)
{
uint8_t x_1247; 
x_1247 = !lean_is_exclusive(x_1233);
if (x_1247 == 0)
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1248 = lean_ctor_get(x_1233, 5);
lean_dec(x_1248);
x_1249 = lean_ctor_get(x_1233, 4);
lean_dec(x_1249);
x_1250 = lean_ctor_get(x_1233, 3);
lean_dec(x_1250);
x_1251 = lean_ctor_get(x_1233, 2);
lean_dec(x_1251);
x_1252 = lean_ctor_get(x_1233, 1);
lean_dec(x_1252);
x_1253 = lean_ctor_get(x_1233, 0);
lean_dec(x_1253);
x_1254 = lean_ctor_get(x_1246, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1246, 1);
lean_inc(x_1255);
lean_dec(x_1246);
lean_ctor_set(x_1233, 5, x_1255);
x_5 = x_1254;
x_6 = x_1233;
goto block_33;
}
else
{
lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_1233);
x_1256 = lean_ctor_get(x_1246, 0);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_1246, 1);
lean_inc(x_1257);
lean_dec(x_1246);
x_1258 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1258, 0, x_1235);
lean_ctor_set(x_1258, 1, x_1236);
lean_ctor_set(x_1258, 2, x_1237);
lean_ctor_set(x_1258, 3, x_1238);
lean_ctor_set(x_1258, 4, x_1239);
lean_ctor_set(x_1258, 5, x_1257);
x_5 = x_1256;
x_6 = x_1258;
goto block_33;
}
}
else
{
lean_object* x_1259; 
lean_dec(x_1239);
lean_dec(x_1238);
lean_dec(x_1237);
lean_dec(x_1236);
lean_dec(x_1235);
lean_dec(x_2);
lean_dec(x_1);
x_1259 = lean_ctor_get(x_1246, 0);
lean_inc(x_1259);
lean_dec(x_1246);
if (lean_obj_tag(x_1259) == 0)
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; 
x_1260 = lean_ctor_get(x_1259, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1259, 1);
lean_inc(x_1261);
lean_dec(x_1259);
x_1262 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1262, 0, x_1261);
x_1263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1263, 0, x_1262);
x_1264 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1260, x_1263, x_3, x_1233);
lean_dec(x_1260);
x_1265 = !lean_is_exclusive(x_1264);
if (x_1265 == 0)
{
return x_1264;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1266 = lean_ctor_get(x_1264, 0);
x_1267 = lean_ctor_get(x_1264, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1264);
x_1268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
return x_1268;
}
}
else
{
lean_object* x_1269; uint8_t x_1270; 
lean_dec(x_3);
x_1269 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1233);
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
}
}
else
{
lean_object* x_1274; lean_object* x_1275; uint8_t x_1276; 
x_1274 = l_Lean_Syntax_getArg(x_1227, x_128);
x_1275 = l_Lean_identKind___closed__2;
lean_inc(x_1274);
x_1276 = l_Lean_Syntax_isOfKind(x_1274, x_1275);
if (x_1276 == 0)
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
lean_dec(x_1274);
lean_dec(x_1227);
lean_dec(x_1133);
lean_dec(x_223);
x_1277 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
lean_dec(x_1277);
x_1280 = l_Lean_Elab_Term_getEnv___rarg(x_1279);
x_1281 = lean_ctor_get(x_1280, 1);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1280, 0);
lean_inc(x_1282);
lean_dec(x_1280);
x_1283 = lean_ctor_get(x_1281, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1281, 1);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_1281, 2);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1281, 3);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1281, 4);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1281, 5);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_3, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1289, 3);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 4);
lean_inc(x_1291);
lean_dec(x_1289);
x_1292 = lean_environment_main_module(x_1282);
x_1293 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1293, 0, x_1292);
lean_ctor_set(x_1293, 1, x_1278);
lean_ctor_set(x_1293, 2, x_1290);
lean_ctor_set(x_1293, 3, x_1291);
lean_inc(x_1);
x_1294 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1293, x_1288);
if (lean_obj_tag(x_1294) == 0)
{
uint8_t x_1295; 
x_1295 = !lean_is_exclusive(x_1281);
if (x_1295 == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1296 = lean_ctor_get(x_1281, 5);
lean_dec(x_1296);
x_1297 = lean_ctor_get(x_1281, 4);
lean_dec(x_1297);
x_1298 = lean_ctor_get(x_1281, 3);
lean_dec(x_1298);
x_1299 = lean_ctor_get(x_1281, 2);
lean_dec(x_1299);
x_1300 = lean_ctor_get(x_1281, 1);
lean_dec(x_1300);
x_1301 = lean_ctor_get(x_1281, 0);
lean_dec(x_1301);
x_1302 = lean_ctor_get(x_1294, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1294, 1);
lean_inc(x_1303);
lean_dec(x_1294);
lean_ctor_set(x_1281, 5, x_1303);
x_5 = x_1302;
x_6 = x_1281;
goto block_33;
}
else
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_1281);
x_1304 = lean_ctor_get(x_1294, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1294, 1);
lean_inc(x_1305);
lean_dec(x_1294);
x_1306 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1306, 0, x_1283);
lean_ctor_set(x_1306, 1, x_1284);
lean_ctor_set(x_1306, 2, x_1285);
lean_ctor_set(x_1306, 3, x_1286);
lean_ctor_set(x_1306, 4, x_1287);
lean_ctor_set(x_1306, 5, x_1305);
x_5 = x_1304;
x_6 = x_1306;
goto block_33;
}
}
else
{
lean_object* x_1307; 
lean_dec(x_1287);
lean_dec(x_1286);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1283);
lean_dec(x_2);
lean_dec(x_1);
x_1307 = lean_ctor_get(x_1294, 0);
lean_inc(x_1307);
lean_dec(x_1294);
if (lean_obj_tag(x_1307) == 0)
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; uint8_t x_1313; 
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
lean_dec(x_1307);
x_1310 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1310, 0, x_1309);
x_1311 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1311, 0, x_1310);
x_1312 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1308, x_1311, x_3, x_1281);
lean_dec(x_1308);
x_1313 = !lean_is_exclusive(x_1312);
if (x_1313 == 0)
{
return x_1312;
}
else
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1314 = lean_ctor_get(x_1312, 0);
x_1315 = lean_ctor_get(x_1312, 1);
lean_inc(x_1315);
lean_inc(x_1314);
lean_dec(x_1312);
x_1316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1316, 0, x_1314);
lean_ctor_set(x_1316, 1, x_1315);
return x_1316;
}
}
else
{
lean_object* x_1317; uint8_t x_1318; 
lean_dec(x_3);
x_1317 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1281);
x_1318 = !lean_is_exclusive(x_1317);
if (x_1318 == 0)
{
return x_1317;
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
x_1319 = lean_ctor_get(x_1317, 0);
x_1320 = lean_ctor_get(x_1317, 1);
lean_inc(x_1320);
lean_inc(x_1319);
lean_dec(x_1317);
x_1321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1321, 0, x_1319);
lean_ctor_set(x_1321, 1, x_1320);
return x_1321;
}
}
}
}
else
{
lean_object* x_1322; uint8_t x_1323; uint8_t x_1372; 
x_1322 = l_Lean_Syntax_getArg(x_1227, x_80);
lean_dec(x_1227);
lean_inc(x_1322);
x_1372 = l_Lean_Syntax_isOfKind(x_1322, x_1030);
if (x_1372 == 0)
{
uint8_t x_1373; 
lean_dec(x_1322);
x_1373 = 0;
x_1323 = x_1373;
goto block_1371;
}
else
{
lean_object* x_1374; lean_object* x_1375; uint8_t x_1376; 
x_1374 = l_Lean_Syntax_getArgs(x_1322);
lean_dec(x_1322);
x_1375 = lean_array_get_size(x_1374);
lean_dec(x_1374);
x_1376 = lean_nat_dec_eq(x_1375, x_128);
lean_dec(x_1375);
x_1323 = x_1376;
goto block_1371;
}
block_1371:
{
if (x_1323 == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
lean_dec(x_1274);
lean_dec(x_1133);
lean_dec(x_223);
x_1324 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1325 = lean_ctor_get(x_1324, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1324, 1);
lean_inc(x_1326);
lean_dec(x_1324);
x_1327 = l_Lean_Elab_Term_getEnv___rarg(x_1326);
x_1328 = lean_ctor_get(x_1327, 1);
lean_inc(x_1328);
x_1329 = lean_ctor_get(x_1327, 0);
lean_inc(x_1329);
lean_dec(x_1327);
x_1330 = lean_ctor_get(x_1328, 0);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1328, 1);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1328, 2);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1328, 3);
lean_inc(x_1333);
x_1334 = lean_ctor_get(x_1328, 4);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1328, 5);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_3, 0);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1336, 3);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1336, 4);
lean_inc(x_1338);
lean_dec(x_1336);
x_1339 = lean_environment_main_module(x_1329);
x_1340 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1340, 0, x_1339);
lean_ctor_set(x_1340, 1, x_1325);
lean_ctor_set(x_1340, 2, x_1337);
lean_ctor_set(x_1340, 3, x_1338);
lean_inc(x_1);
x_1341 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1340, x_1335);
if (lean_obj_tag(x_1341) == 0)
{
uint8_t x_1342; 
x_1342 = !lean_is_exclusive(x_1328);
if (x_1342 == 0)
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1343 = lean_ctor_get(x_1328, 5);
lean_dec(x_1343);
x_1344 = lean_ctor_get(x_1328, 4);
lean_dec(x_1344);
x_1345 = lean_ctor_get(x_1328, 3);
lean_dec(x_1345);
x_1346 = lean_ctor_get(x_1328, 2);
lean_dec(x_1346);
x_1347 = lean_ctor_get(x_1328, 1);
lean_dec(x_1347);
x_1348 = lean_ctor_get(x_1328, 0);
lean_dec(x_1348);
x_1349 = lean_ctor_get(x_1341, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1341, 1);
lean_inc(x_1350);
lean_dec(x_1341);
lean_ctor_set(x_1328, 5, x_1350);
x_5 = x_1349;
x_6 = x_1328;
goto block_33;
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
lean_dec(x_1328);
x_1351 = lean_ctor_get(x_1341, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1341, 1);
lean_inc(x_1352);
lean_dec(x_1341);
x_1353 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1353, 0, x_1330);
lean_ctor_set(x_1353, 1, x_1331);
lean_ctor_set(x_1353, 2, x_1332);
lean_ctor_set(x_1353, 3, x_1333);
lean_ctor_set(x_1353, 4, x_1334);
lean_ctor_set(x_1353, 5, x_1352);
x_5 = x_1351;
x_6 = x_1353;
goto block_33;
}
}
else
{
lean_object* x_1354; 
lean_dec(x_1334);
lean_dec(x_1333);
lean_dec(x_1332);
lean_dec(x_1331);
lean_dec(x_1330);
lean_dec(x_2);
lean_dec(x_1);
x_1354 = lean_ctor_get(x_1341, 0);
lean_inc(x_1354);
lean_dec(x_1341);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; uint8_t x_1360; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
lean_dec(x_1354);
x_1357 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1357, 0, x_1356);
x_1358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1358, 0, x_1357);
x_1359 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1355, x_1358, x_3, x_1328);
lean_dec(x_1355);
x_1360 = !lean_is_exclusive(x_1359);
if (x_1360 == 0)
{
return x_1359;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1361 = lean_ctor_get(x_1359, 0);
x_1362 = lean_ctor_get(x_1359, 1);
lean_inc(x_1362);
lean_inc(x_1361);
lean_dec(x_1359);
x_1363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1363, 0, x_1361);
lean_ctor_set(x_1363, 1, x_1362);
return x_1363;
}
}
else
{
lean_object* x_1364; uint8_t x_1365; 
lean_dec(x_3);
x_1364 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1328);
x_1365 = !lean_is_exclusive(x_1364);
if (x_1365 == 0)
{
return x_1364;
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
x_1366 = lean_ctor_get(x_1364, 0);
x_1367 = lean_ctor_get(x_1364, 1);
lean_inc(x_1367);
lean_inc(x_1366);
lean_dec(x_1364);
x_1368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1368, 0, x_1366);
lean_ctor_set(x_1368, 1, x_1367);
return x_1368;
}
}
}
}
else
{
lean_object* x_1369; lean_object* x_1370; 
x_1369 = l_Lean_Syntax_getArg(x_1133, x_224);
lean_dec(x_1133);
x_1370 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_223, x_1274, x_1369, x_2, x_3, x_4);
return x_1370;
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
block_1730:
{
if (x_1406 == 0)
{
if (x_1405 == 0)
{
uint8_t x_1407; 
lean_dec(x_1038);
x_1407 = 0;
x_1039 = x_1407;
goto block_1404;
}
else
{
lean_object* x_1408; lean_object* x_1409; uint8_t x_1410; 
x_1408 = l_Lean_Syntax_getArgs(x_1038);
lean_dec(x_1038);
x_1409 = lean_array_get_size(x_1408);
lean_dec(x_1408);
x_1410 = lean_nat_dec_eq(x_1409, x_80);
lean_dec(x_1409);
x_1039 = x_1410;
goto block_1404;
}
}
else
{
lean_object* x_1411; lean_object* x_1412; uint8_t x_1413; uint8_t x_1725; 
lean_dec(x_1038);
x_1411 = lean_unsigned_to_nat(5u);
x_1412 = l_Lean_Syntax_getArg(x_1, x_1411);
lean_inc(x_1412);
x_1725 = l_Lean_Syntax_isOfKind(x_1412, x_1030);
if (x_1725 == 0)
{
uint8_t x_1726; 
x_1726 = 0;
x_1413 = x_1726;
goto block_1724;
}
else
{
lean_object* x_1727; lean_object* x_1728; uint8_t x_1729; 
x_1727 = l_Lean_Syntax_getArgs(x_1412);
x_1728 = lean_array_get_size(x_1727);
lean_dec(x_1727);
x_1729 = lean_nat_dec_eq(x_1728, x_80);
lean_dec(x_1728);
x_1413 = x_1729;
goto block_1724;
}
block_1724:
{
if (x_1413 == 0)
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
lean_dec(x_1412);
lean_dec(x_223);
x_1414 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
lean_dec(x_1414);
x_1417 = l_Lean_Elab_Term_getEnv___rarg(x_1416);
x_1418 = lean_ctor_get(x_1417, 1);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1417, 0);
lean_inc(x_1419);
lean_dec(x_1417);
x_1420 = lean_ctor_get(x_1418, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1418, 1);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1418, 2);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1418, 3);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1418, 4);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1418, 5);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_3, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1426, 3);
lean_inc(x_1427);
x_1428 = lean_ctor_get(x_1426, 4);
lean_inc(x_1428);
lean_dec(x_1426);
x_1429 = lean_environment_main_module(x_1419);
x_1430 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1430, 0, x_1429);
lean_ctor_set(x_1430, 1, x_1415);
lean_ctor_set(x_1430, 2, x_1427);
lean_ctor_set(x_1430, 3, x_1428);
lean_inc(x_1);
x_1431 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1430, x_1425);
if (lean_obj_tag(x_1431) == 0)
{
uint8_t x_1432; 
x_1432 = !lean_is_exclusive(x_1418);
if (x_1432 == 0)
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1433 = lean_ctor_get(x_1418, 5);
lean_dec(x_1433);
x_1434 = lean_ctor_get(x_1418, 4);
lean_dec(x_1434);
x_1435 = lean_ctor_get(x_1418, 3);
lean_dec(x_1435);
x_1436 = lean_ctor_get(x_1418, 2);
lean_dec(x_1436);
x_1437 = lean_ctor_get(x_1418, 1);
lean_dec(x_1437);
x_1438 = lean_ctor_get(x_1418, 0);
lean_dec(x_1438);
x_1439 = lean_ctor_get(x_1431, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1431, 1);
lean_inc(x_1440);
lean_dec(x_1431);
lean_ctor_set(x_1418, 5, x_1440);
x_5 = x_1439;
x_6 = x_1418;
goto block_33;
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
lean_dec(x_1418);
x_1441 = lean_ctor_get(x_1431, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1431, 1);
lean_inc(x_1442);
lean_dec(x_1431);
x_1443 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1443, 0, x_1420);
lean_ctor_set(x_1443, 1, x_1421);
lean_ctor_set(x_1443, 2, x_1422);
lean_ctor_set(x_1443, 3, x_1423);
lean_ctor_set(x_1443, 4, x_1424);
lean_ctor_set(x_1443, 5, x_1442);
x_5 = x_1441;
x_6 = x_1443;
goto block_33;
}
}
else
{
lean_object* x_1444; 
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_1422);
lean_dec(x_1421);
lean_dec(x_1420);
lean_dec(x_2);
lean_dec(x_1);
x_1444 = lean_ctor_get(x_1431, 0);
lean_inc(x_1444);
lean_dec(x_1431);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; uint8_t x_1450; 
x_1445 = lean_ctor_get(x_1444, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1444, 1);
lean_inc(x_1446);
lean_dec(x_1444);
x_1447 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1447, 0, x_1446);
x_1448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1448, 0, x_1447);
x_1449 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1445, x_1448, x_3, x_1418);
lean_dec(x_1445);
x_1450 = !lean_is_exclusive(x_1449);
if (x_1450 == 0)
{
return x_1449;
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
x_1451 = lean_ctor_get(x_1449, 0);
x_1452 = lean_ctor_get(x_1449, 1);
lean_inc(x_1452);
lean_inc(x_1451);
lean_dec(x_1449);
x_1453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1453, 0, x_1451);
lean_ctor_set(x_1453, 1, x_1452);
return x_1453;
}
}
else
{
lean_object* x_1454; uint8_t x_1455; 
lean_dec(x_3);
x_1454 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1418);
x_1455 = !lean_is_exclusive(x_1454);
if (x_1455 == 0)
{
return x_1454;
}
else
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1456 = lean_ctor_get(x_1454, 0);
x_1457 = lean_ctor_get(x_1454, 1);
lean_inc(x_1457);
lean_inc(x_1456);
lean_dec(x_1454);
x_1458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1458, 0, x_1456);
lean_ctor_set(x_1458, 1, x_1457);
return x_1458;
}
}
}
}
else
{
lean_object* x_1459; uint8_t x_1460; lean_object* x_1717; uint8_t x_1718; 
x_1459 = l_Lean_Syntax_getArg(x_1412, x_128);
lean_dec(x_1412);
x_1717 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_1459);
x_1718 = l_Lean_Syntax_isOfKind(x_1459, x_1717);
if (x_1718 == 0)
{
uint8_t x_1719; 
x_1719 = 0;
x_1460 = x_1719;
goto block_1716;
}
else
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; uint8_t x_1723; 
x_1720 = l_Lean_Syntax_getArgs(x_1459);
x_1721 = lean_array_get_size(x_1720);
lean_dec(x_1720);
x_1722 = lean_unsigned_to_nat(3u);
x_1723 = lean_nat_dec_eq(x_1721, x_1722);
lean_dec(x_1721);
x_1460 = x_1723;
goto block_1716;
}
block_1716:
{
if (x_1460 == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
lean_dec(x_1459);
lean_dec(x_223);
x_1461 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1462 = lean_ctor_get(x_1461, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1461, 1);
lean_inc(x_1463);
lean_dec(x_1461);
x_1464 = l_Lean_Elab_Term_getEnv___rarg(x_1463);
x_1465 = lean_ctor_get(x_1464, 1);
lean_inc(x_1465);
x_1466 = lean_ctor_get(x_1464, 0);
lean_inc(x_1466);
lean_dec(x_1464);
x_1467 = lean_ctor_get(x_1465, 0);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1465, 1);
lean_inc(x_1468);
x_1469 = lean_ctor_get(x_1465, 2);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1465, 3);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1465, 4);
lean_inc(x_1471);
x_1472 = lean_ctor_get(x_1465, 5);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_3, 0);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1473, 3);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1473, 4);
lean_inc(x_1475);
lean_dec(x_1473);
x_1476 = lean_environment_main_module(x_1466);
x_1477 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1477, 0, x_1476);
lean_ctor_set(x_1477, 1, x_1462);
lean_ctor_set(x_1477, 2, x_1474);
lean_ctor_set(x_1477, 3, x_1475);
lean_inc(x_1);
x_1478 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1477, x_1472);
if (lean_obj_tag(x_1478) == 0)
{
uint8_t x_1479; 
x_1479 = !lean_is_exclusive(x_1465);
if (x_1479 == 0)
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
x_1480 = lean_ctor_get(x_1465, 5);
lean_dec(x_1480);
x_1481 = lean_ctor_get(x_1465, 4);
lean_dec(x_1481);
x_1482 = lean_ctor_get(x_1465, 3);
lean_dec(x_1482);
x_1483 = lean_ctor_get(x_1465, 2);
lean_dec(x_1483);
x_1484 = lean_ctor_get(x_1465, 1);
lean_dec(x_1484);
x_1485 = lean_ctor_get(x_1465, 0);
lean_dec(x_1485);
x_1486 = lean_ctor_get(x_1478, 0);
lean_inc(x_1486);
x_1487 = lean_ctor_get(x_1478, 1);
lean_inc(x_1487);
lean_dec(x_1478);
lean_ctor_set(x_1465, 5, x_1487);
x_5 = x_1486;
x_6 = x_1465;
goto block_33;
}
else
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
lean_dec(x_1465);
x_1488 = lean_ctor_get(x_1478, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1478, 1);
lean_inc(x_1489);
lean_dec(x_1478);
x_1490 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1490, 0, x_1467);
lean_ctor_set(x_1490, 1, x_1468);
lean_ctor_set(x_1490, 2, x_1469);
lean_ctor_set(x_1490, 3, x_1470);
lean_ctor_set(x_1490, 4, x_1471);
lean_ctor_set(x_1490, 5, x_1489);
x_5 = x_1488;
x_6 = x_1490;
goto block_33;
}
}
else
{
lean_object* x_1491; 
lean_dec(x_1471);
lean_dec(x_1470);
lean_dec(x_1469);
lean_dec(x_1468);
lean_dec(x_1467);
lean_dec(x_2);
lean_dec(x_1);
x_1491 = lean_ctor_get(x_1478, 0);
lean_inc(x_1491);
lean_dec(x_1478);
if (lean_obj_tag(x_1491) == 0)
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; uint8_t x_1497; 
x_1492 = lean_ctor_get(x_1491, 0);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1491, 1);
lean_inc(x_1493);
lean_dec(x_1491);
x_1494 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1494, 0, x_1493);
x_1495 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1495, 0, x_1494);
x_1496 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1492, x_1495, x_3, x_1465);
lean_dec(x_1492);
x_1497 = !lean_is_exclusive(x_1496);
if (x_1497 == 0)
{
return x_1496;
}
else
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
x_1498 = lean_ctor_get(x_1496, 0);
x_1499 = lean_ctor_get(x_1496, 1);
lean_inc(x_1499);
lean_inc(x_1498);
lean_dec(x_1496);
x_1500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1500, 0, x_1498);
lean_ctor_set(x_1500, 1, x_1499);
return x_1500;
}
}
else
{
lean_object* x_1501; uint8_t x_1502; 
lean_dec(x_3);
x_1501 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1465);
x_1502 = !lean_is_exclusive(x_1501);
if (x_1502 == 0)
{
return x_1501;
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1503 = lean_ctor_get(x_1501, 0);
x_1504 = lean_ctor_get(x_1501, 1);
lean_inc(x_1504);
lean_inc(x_1503);
lean_dec(x_1501);
x_1505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1505, 0, x_1503);
lean_ctor_set(x_1505, 1, x_1504);
return x_1505;
}
}
}
}
else
{
lean_object* x_1506; uint8_t x_1507; uint8_t x_1711; 
x_1506 = l_Lean_Syntax_getArg(x_1459, x_128);
lean_inc(x_1506);
x_1711 = l_Lean_Syntax_isOfKind(x_1506, x_1030);
if (x_1711 == 0)
{
uint8_t x_1712; 
x_1712 = 0;
x_1507 = x_1712;
goto block_1710;
}
else
{
lean_object* x_1713; lean_object* x_1714; uint8_t x_1715; 
x_1713 = l_Lean_Syntax_getArgs(x_1506);
x_1714 = lean_array_get_size(x_1713);
lean_dec(x_1713);
x_1715 = lean_nat_dec_eq(x_1714, x_80);
lean_dec(x_1714);
x_1507 = x_1715;
goto block_1710;
}
block_1710:
{
if (x_1507 == 0)
{
lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
lean_dec(x_1506);
lean_dec(x_1459);
lean_dec(x_223);
x_1508 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1509 = lean_ctor_get(x_1508, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1508, 1);
lean_inc(x_1510);
lean_dec(x_1508);
x_1511 = l_Lean_Elab_Term_getEnv___rarg(x_1510);
x_1512 = lean_ctor_get(x_1511, 1);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1511, 0);
lean_inc(x_1513);
lean_dec(x_1511);
x_1514 = lean_ctor_get(x_1512, 0);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1512, 1);
lean_inc(x_1515);
x_1516 = lean_ctor_get(x_1512, 2);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1512, 3);
lean_inc(x_1517);
x_1518 = lean_ctor_get(x_1512, 4);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1512, 5);
lean_inc(x_1519);
x_1520 = lean_ctor_get(x_3, 0);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_1520, 3);
lean_inc(x_1521);
x_1522 = lean_ctor_get(x_1520, 4);
lean_inc(x_1522);
lean_dec(x_1520);
x_1523 = lean_environment_main_module(x_1513);
x_1524 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1524, 0, x_1523);
lean_ctor_set(x_1524, 1, x_1509);
lean_ctor_set(x_1524, 2, x_1521);
lean_ctor_set(x_1524, 3, x_1522);
lean_inc(x_1);
x_1525 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1524, x_1519);
if (lean_obj_tag(x_1525) == 0)
{
uint8_t x_1526; 
x_1526 = !lean_is_exclusive(x_1512);
if (x_1526 == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1527 = lean_ctor_get(x_1512, 5);
lean_dec(x_1527);
x_1528 = lean_ctor_get(x_1512, 4);
lean_dec(x_1528);
x_1529 = lean_ctor_get(x_1512, 3);
lean_dec(x_1529);
x_1530 = lean_ctor_get(x_1512, 2);
lean_dec(x_1530);
x_1531 = lean_ctor_get(x_1512, 1);
lean_dec(x_1531);
x_1532 = lean_ctor_get(x_1512, 0);
lean_dec(x_1532);
x_1533 = lean_ctor_get(x_1525, 0);
lean_inc(x_1533);
x_1534 = lean_ctor_get(x_1525, 1);
lean_inc(x_1534);
lean_dec(x_1525);
lean_ctor_set(x_1512, 5, x_1534);
x_5 = x_1533;
x_6 = x_1512;
goto block_33;
}
else
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; 
lean_dec(x_1512);
x_1535 = lean_ctor_get(x_1525, 0);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1525, 1);
lean_inc(x_1536);
lean_dec(x_1525);
x_1537 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1537, 0, x_1514);
lean_ctor_set(x_1537, 1, x_1515);
lean_ctor_set(x_1537, 2, x_1516);
lean_ctor_set(x_1537, 3, x_1517);
lean_ctor_set(x_1537, 4, x_1518);
lean_ctor_set(x_1537, 5, x_1536);
x_5 = x_1535;
x_6 = x_1537;
goto block_33;
}
}
else
{
lean_object* x_1538; 
lean_dec(x_1518);
lean_dec(x_1517);
lean_dec(x_1516);
lean_dec(x_1515);
lean_dec(x_1514);
lean_dec(x_2);
lean_dec(x_1);
x_1538 = lean_ctor_get(x_1525, 0);
lean_inc(x_1538);
lean_dec(x_1525);
if (lean_obj_tag(x_1538) == 0)
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; uint8_t x_1544; 
x_1539 = lean_ctor_get(x_1538, 0);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_1538, 1);
lean_inc(x_1540);
lean_dec(x_1538);
x_1541 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1541, 0, x_1540);
x_1542 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1542, 0, x_1541);
x_1543 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1539, x_1542, x_3, x_1512);
lean_dec(x_1539);
x_1544 = !lean_is_exclusive(x_1543);
if (x_1544 == 0)
{
return x_1543;
}
else
{
lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
x_1545 = lean_ctor_get(x_1543, 0);
x_1546 = lean_ctor_get(x_1543, 1);
lean_inc(x_1546);
lean_inc(x_1545);
lean_dec(x_1543);
x_1547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1547, 0, x_1545);
lean_ctor_set(x_1547, 1, x_1546);
return x_1547;
}
}
else
{
lean_object* x_1548; uint8_t x_1549; 
lean_dec(x_3);
x_1548 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1512);
x_1549 = !lean_is_exclusive(x_1548);
if (x_1549 == 0)
{
return x_1548;
}
else
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; 
x_1550 = lean_ctor_get(x_1548, 0);
x_1551 = lean_ctor_get(x_1548, 1);
lean_inc(x_1551);
lean_inc(x_1550);
lean_dec(x_1548);
x_1552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1552, 0, x_1550);
lean_ctor_set(x_1552, 1, x_1551);
return x_1552;
}
}
}
}
else
{
lean_object* x_1553; uint8_t x_1554; lean_object* x_1704; uint8_t x_1705; 
x_1553 = l_Lean_Syntax_getArg(x_1506, x_128);
lean_dec(x_1506);
x_1704 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_1553);
x_1705 = l_Lean_Syntax_isOfKind(x_1553, x_1704);
if (x_1705 == 0)
{
uint8_t x_1706; 
x_1706 = 0;
x_1554 = x_1706;
goto block_1703;
}
else
{
lean_object* x_1707; lean_object* x_1708; uint8_t x_1709; 
x_1707 = l_Lean_Syntax_getArgs(x_1553);
x_1708 = lean_array_get_size(x_1707);
lean_dec(x_1707);
x_1709 = lean_nat_dec_eq(x_1708, x_224);
lean_dec(x_1708);
x_1554 = x_1709;
goto block_1703;
}
block_1703:
{
if (x_1554 == 0)
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
lean_dec(x_1553);
lean_dec(x_1459);
lean_dec(x_223);
x_1555 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1555, 1);
lean_inc(x_1557);
lean_dec(x_1555);
x_1558 = l_Lean_Elab_Term_getEnv___rarg(x_1557);
x_1559 = lean_ctor_get(x_1558, 1);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1558, 0);
lean_inc(x_1560);
lean_dec(x_1558);
x_1561 = lean_ctor_get(x_1559, 0);
lean_inc(x_1561);
x_1562 = lean_ctor_get(x_1559, 1);
lean_inc(x_1562);
x_1563 = lean_ctor_get(x_1559, 2);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1559, 3);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1559, 4);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1559, 5);
lean_inc(x_1566);
x_1567 = lean_ctor_get(x_3, 0);
lean_inc(x_1567);
x_1568 = lean_ctor_get(x_1567, 3);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1567, 4);
lean_inc(x_1569);
lean_dec(x_1567);
x_1570 = lean_environment_main_module(x_1560);
x_1571 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1571, 0, x_1570);
lean_ctor_set(x_1571, 1, x_1556);
lean_ctor_set(x_1571, 2, x_1568);
lean_ctor_set(x_1571, 3, x_1569);
lean_inc(x_1);
x_1572 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1571, x_1566);
if (lean_obj_tag(x_1572) == 0)
{
uint8_t x_1573; 
x_1573 = !lean_is_exclusive(x_1559);
if (x_1573 == 0)
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
x_1574 = lean_ctor_get(x_1559, 5);
lean_dec(x_1574);
x_1575 = lean_ctor_get(x_1559, 4);
lean_dec(x_1575);
x_1576 = lean_ctor_get(x_1559, 3);
lean_dec(x_1576);
x_1577 = lean_ctor_get(x_1559, 2);
lean_dec(x_1577);
x_1578 = lean_ctor_get(x_1559, 1);
lean_dec(x_1578);
x_1579 = lean_ctor_get(x_1559, 0);
lean_dec(x_1579);
x_1580 = lean_ctor_get(x_1572, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1572, 1);
lean_inc(x_1581);
lean_dec(x_1572);
lean_ctor_set(x_1559, 5, x_1581);
x_5 = x_1580;
x_6 = x_1559;
goto block_33;
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; 
lean_dec(x_1559);
x_1582 = lean_ctor_get(x_1572, 0);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1572, 1);
lean_inc(x_1583);
lean_dec(x_1572);
x_1584 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1584, 0, x_1561);
lean_ctor_set(x_1584, 1, x_1562);
lean_ctor_set(x_1584, 2, x_1563);
lean_ctor_set(x_1584, 3, x_1564);
lean_ctor_set(x_1584, 4, x_1565);
lean_ctor_set(x_1584, 5, x_1583);
x_5 = x_1582;
x_6 = x_1584;
goto block_33;
}
}
else
{
lean_object* x_1585; 
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_1563);
lean_dec(x_1562);
lean_dec(x_1561);
lean_dec(x_2);
lean_dec(x_1);
x_1585 = lean_ctor_get(x_1572, 0);
lean_inc(x_1585);
lean_dec(x_1572);
if (lean_obj_tag(x_1585) == 0)
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; 
x_1586 = lean_ctor_get(x_1585, 0);
lean_inc(x_1586);
x_1587 = lean_ctor_get(x_1585, 1);
lean_inc(x_1587);
lean_dec(x_1585);
x_1588 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1588, 0, x_1587);
x_1589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1589, 0, x_1588);
x_1590 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1586, x_1589, x_3, x_1559);
lean_dec(x_1586);
x_1591 = !lean_is_exclusive(x_1590);
if (x_1591 == 0)
{
return x_1590;
}
else
{
lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; 
x_1592 = lean_ctor_get(x_1590, 0);
x_1593 = lean_ctor_get(x_1590, 1);
lean_inc(x_1593);
lean_inc(x_1592);
lean_dec(x_1590);
x_1594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1594, 0, x_1592);
lean_ctor_set(x_1594, 1, x_1593);
return x_1594;
}
}
else
{
lean_object* x_1595; uint8_t x_1596; 
lean_dec(x_3);
x_1595 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1559);
x_1596 = !lean_is_exclusive(x_1595);
if (x_1596 == 0)
{
return x_1595;
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1597 = lean_ctor_get(x_1595, 0);
x_1598 = lean_ctor_get(x_1595, 1);
lean_inc(x_1598);
lean_inc(x_1597);
lean_dec(x_1595);
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
lean_object* x_1600; lean_object* x_1601; uint8_t x_1602; 
x_1600 = l_Lean_Syntax_getArg(x_1553, x_128);
x_1601 = l_Lean_identKind___closed__2;
lean_inc(x_1600);
x_1602 = l_Lean_Syntax_isOfKind(x_1600, x_1601);
if (x_1602 == 0)
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
lean_dec(x_1600);
lean_dec(x_1553);
lean_dec(x_1459);
lean_dec(x_223);
x_1603 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1604 = lean_ctor_get(x_1603, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1603, 1);
lean_inc(x_1605);
lean_dec(x_1603);
x_1606 = l_Lean_Elab_Term_getEnv___rarg(x_1605);
x_1607 = lean_ctor_get(x_1606, 1);
lean_inc(x_1607);
x_1608 = lean_ctor_get(x_1606, 0);
lean_inc(x_1608);
lean_dec(x_1606);
x_1609 = lean_ctor_get(x_1607, 0);
lean_inc(x_1609);
x_1610 = lean_ctor_get(x_1607, 1);
lean_inc(x_1610);
x_1611 = lean_ctor_get(x_1607, 2);
lean_inc(x_1611);
x_1612 = lean_ctor_get(x_1607, 3);
lean_inc(x_1612);
x_1613 = lean_ctor_get(x_1607, 4);
lean_inc(x_1613);
x_1614 = lean_ctor_get(x_1607, 5);
lean_inc(x_1614);
x_1615 = lean_ctor_get(x_3, 0);
lean_inc(x_1615);
x_1616 = lean_ctor_get(x_1615, 3);
lean_inc(x_1616);
x_1617 = lean_ctor_get(x_1615, 4);
lean_inc(x_1617);
lean_dec(x_1615);
x_1618 = lean_environment_main_module(x_1608);
x_1619 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1619, 0, x_1618);
lean_ctor_set(x_1619, 1, x_1604);
lean_ctor_set(x_1619, 2, x_1616);
lean_ctor_set(x_1619, 3, x_1617);
lean_inc(x_1);
x_1620 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1619, x_1614);
if (lean_obj_tag(x_1620) == 0)
{
uint8_t x_1621; 
x_1621 = !lean_is_exclusive(x_1607);
if (x_1621 == 0)
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1622 = lean_ctor_get(x_1607, 5);
lean_dec(x_1622);
x_1623 = lean_ctor_get(x_1607, 4);
lean_dec(x_1623);
x_1624 = lean_ctor_get(x_1607, 3);
lean_dec(x_1624);
x_1625 = lean_ctor_get(x_1607, 2);
lean_dec(x_1625);
x_1626 = lean_ctor_get(x_1607, 1);
lean_dec(x_1626);
x_1627 = lean_ctor_get(x_1607, 0);
lean_dec(x_1627);
x_1628 = lean_ctor_get(x_1620, 0);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1620, 1);
lean_inc(x_1629);
lean_dec(x_1620);
lean_ctor_set(x_1607, 5, x_1629);
x_5 = x_1628;
x_6 = x_1607;
goto block_33;
}
else
{
lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; 
lean_dec(x_1607);
x_1630 = lean_ctor_get(x_1620, 0);
lean_inc(x_1630);
x_1631 = lean_ctor_get(x_1620, 1);
lean_inc(x_1631);
lean_dec(x_1620);
x_1632 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1632, 0, x_1609);
lean_ctor_set(x_1632, 1, x_1610);
lean_ctor_set(x_1632, 2, x_1611);
lean_ctor_set(x_1632, 3, x_1612);
lean_ctor_set(x_1632, 4, x_1613);
lean_ctor_set(x_1632, 5, x_1631);
x_5 = x_1630;
x_6 = x_1632;
goto block_33;
}
}
else
{
lean_object* x_1633; 
lean_dec(x_1613);
lean_dec(x_1612);
lean_dec(x_1611);
lean_dec(x_1610);
lean_dec(x_1609);
lean_dec(x_2);
lean_dec(x_1);
x_1633 = lean_ctor_get(x_1620, 0);
lean_inc(x_1633);
lean_dec(x_1620);
if (lean_obj_tag(x_1633) == 0)
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; uint8_t x_1639; 
x_1634 = lean_ctor_get(x_1633, 0);
lean_inc(x_1634);
x_1635 = lean_ctor_get(x_1633, 1);
lean_inc(x_1635);
lean_dec(x_1633);
x_1636 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1636, 0, x_1635);
x_1637 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1637, 0, x_1636);
x_1638 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1634, x_1637, x_3, x_1607);
lean_dec(x_1634);
x_1639 = !lean_is_exclusive(x_1638);
if (x_1639 == 0)
{
return x_1638;
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
x_1640 = lean_ctor_get(x_1638, 0);
x_1641 = lean_ctor_get(x_1638, 1);
lean_inc(x_1641);
lean_inc(x_1640);
lean_dec(x_1638);
x_1642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1642, 0, x_1640);
lean_ctor_set(x_1642, 1, x_1641);
return x_1642;
}
}
else
{
lean_object* x_1643; uint8_t x_1644; 
lean_dec(x_3);
x_1643 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1607);
x_1644 = !lean_is_exclusive(x_1643);
if (x_1644 == 0)
{
return x_1643;
}
else
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
x_1645 = lean_ctor_get(x_1643, 0);
x_1646 = lean_ctor_get(x_1643, 1);
lean_inc(x_1646);
lean_inc(x_1645);
lean_dec(x_1643);
x_1647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1647, 0, x_1645);
lean_ctor_set(x_1647, 1, x_1646);
return x_1647;
}
}
}
}
else
{
lean_object* x_1648; uint8_t x_1649; uint8_t x_1698; 
x_1648 = l_Lean_Syntax_getArg(x_1553, x_80);
lean_dec(x_1553);
lean_inc(x_1648);
x_1698 = l_Lean_Syntax_isOfKind(x_1648, x_1030);
if (x_1698 == 0)
{
uint8_t x_1699; 
lean_dec(x_1648);
x_1699 = 0;
x_1649 = x_1699;
goto block_1697;
}
else
{
lean_object* x_1700; lean_object* x_1701; uint8_t x_1702; 
x_1700 = l_Lean_Syntax_getArgs(x_1648);
lean_dec(x_1648);
x_1701 = lean_array_get_size(x_1700);
lean_dec(x_1700);
x_1702 = lean_nat_dec_eq(x_1701, x_128);
lean_dec(x_1701);
x_1649 = x_1702;
goto block_1697;
}
block_1697:
{
if (x_1649 == 0)
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; 
lean_dec(x_1600);
lean_dec(x_1459);
lean_dec(x_223);
x_1650 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_1651 = lean_ctor_get(x_1650, 0);
lean_inc(x_1651);
x_1652 = lean_ctor_get(x_1650, 1);
lean_inc(x_1652);
lean_dec(x_1650);
x_1653 = l_Lean_Elab_Term_getEnv___rarg(x_1652);
x_1654 = lean_ctor_get(x_1653, 1);
lean_inc(x_1654);
x_1655 = lean_ctor_get(x_1653, 0);
lean_inc(x_1655);
lean_dec(x_1653);
x_1656 = lean_ctor_get(x_1654, 0);
lean_inc(x_1656);
x_1657 = lean_ctor_get(x_1654, 1);
lean_inc(x_1657);
x_1658 = lean_ctor_get(x_1654, 2);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1654, 3);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_1654, 4);
lean_inc(x_1660);
x_1661 = lean_ctor_get(x_1654, 5);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_3, 0);
lean_inc(x_1662);
x_1663 = lean_ctor_get(x_1662, 3);
lean_inc(x_1663);
x_1664 = lean_ctor_get(x_1662, 4);
lean_inc(x_1664);
lean_dec(x_1662);
x_1665 = lean_environment_main_module(x_1655);
x_1666 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1666, 0, x_1665);
lean_ctor_set(x_1666, 1, x_1651);
lean_ctor_set(x_1666, 2, x_1663);
lean_ctor_set(x_1666, 3, x_1664);
lean_inc(x_1);
x_1667 = l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f(x_1, x_1666, x_1661);
if (lean_obj_tag(x_1667) == 0)
{
uint8_t x_1668; 
x_1668 = !lean_is_exclusive(x_1654);
if (x_1668 == 0)
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
x_1669 = lean_ctor_get(x_1654, 5);
lean_dec(x_1669);
x_1670 = lean_ctor_get(x_1654, 4);
lean_dec(x_1670);
x_1671 = lean_ctor_get(x_1654, 3);
lean_dec(x_1671);
x_1672 = lean_ctor_get(x_1654, 2);
lean_dec(x_1672);
x_1673 = lean_ctor_get(x_1654, 1);
lean_dec(x_1673);
x_1674 = lean_ctor_get(x_1654, 0);
lean_dec(x_1674);
x_1675 = lean_ctor_get(x_1667, 0);
lean_inc(x_1675);
x_1676 = lean_ctor_get(x_1667, 1);
lean_inc(x_1676);
lean_dec(x_1667);
lean_ctor_set(x_1654, 5, x_1676);
x_5 = x_1675;
x_6 = x_1654;
goto block_33;
}
else
{
lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; 
lean_dec(x_1654);
x_1677 = lean_ctor_get(x_1667, 0);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_1667, 1);
lean_inc(x_1678);
lean_dec(x_1667);
x_1679 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1679, 0, x_1656);
lean_ctor_set(x_1679, 1, x_1657);
lean_ctor_set(x_1679, 2, x_1658);
lean_ctor_set(x_1679, 3, x_1659);
lean_ctor_set(x_1679, 4, x_1660);
lean_ctor_set(x_1679, 5, x_1678);
x_5 = x_1677;
x_6 = x_1679;
goto block_33;
}
}
else
{
lean_object* x_1680; 
lean_dec(x_1660);
lean_dec(x_1659);
lean_dec(x_1658);
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_2);
lean_dec(x_1);
x_1680 = lean_ctor_get(x_1667, 0);
lean_inc(x_1680);
lean_dec(x_1667);
if (lean_obj_tag(x_1680) == 0)
{
lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; uint8_t x_1686; 
x_1681 = lean_ctor_get(x_1680, 0);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_1680, 1);
lean_inc(x_1682);
lean_dec(x_1680);
x_1683 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1683, 0, x_1682);
x_1684 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1684, 0, x_1683);
x_1685 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1681, x_1684, x_3, x_1654);
lean_dec(x_1681);
x_1686 = !lean_is_exclusive(x_1685);
if (x_1686 == 0)
{
return x_1685;
}
else
{
lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1687 = lean_ctor_get(x_1685, 0);
x_1688 = lean_ctor_get(x_1685, 1);
lean_inc(x_1688);
lean_inc(x_1687);
lean_dec(x_1685);
x_1689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1689, 0, x_1687);
lean_ctor_set(x_1689, 1, x_1688);
return x_1689;
}
}
else
{
lean_object* x_1690; uint8_t x_1691; 
lean_dec(x_3);
x_1690 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_1654);
x_1691 = !lean_is_exclusive(x_1690);
if (x_1691 == 0)
{
return x_1690;
}
else
{
lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; 
x_1692 = lean_ctor_get(x_1690, 0);
x_1693 = lean_ctor_get(x_1690, 1);
lean_inc(x_1693);
lean_inc(x_1692);
lean_dec(x_1690);
x_1694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1694, 0, x_1692);
lean_ctor_set(x_1694, 1, x_1693);
return x_1694;
}
}
}
}
else
{
lean_object* x_1695; lean_object* x_1696; 
x_1695 = l_Lean_Syntax_getArg(x_1459, x_224);
lean_dec(x_1459);
x_1696 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_223, x_1600, x_1695, x_2, x_3, x_4);
return x_1696;
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
x_3 = l_Lean_Parser_Term_match___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_39__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
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
lean_object* initialize_Lean_Meta_EqnCompiler_MatchPattern(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_DepElim(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_MatchPattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_DepElim(lean_io_mk_world());
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
l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__3 = _init_l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_16__processIdAux___lambda__1___closed__3);
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
l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4);
l___private_Lean_Elab_Match_21__collectPatternVars___closed__1 = _init_l___private_Lean_Elab_Match_21__collectPatternVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_21__collectPatternVars___closed__1);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__1);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__2);
l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3 = _init_l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_24__elabPatternsAux___main___closed__3);
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
l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Match_30__elabPatterns___spec__3___closed__3);
l___private_Lean_Elab_Match_30__elabPatterns___closed__1 = _init_l___private_Lean_Elab_Match_30__elabPatterns___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_30__elabPatterns___closed__1);
l___private_Lean_Elab_Match_30__elabPatterns___closed__2 = _init_l___private_Lean_Elab_Match_30__elabPatterns___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_30__elabPatterns___closed__2);
l___private_Lean_Elab_Match_30__elabPatterns___closed__3 = _init_l___private_Lean_Elab_Match_30__elabPatterns___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_30__elabPatterns___closed__3);
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
l___private_Lean_Elab_Match_31__elabMatchCore___closed__1 = _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_31__elabMatchCore___closed__1);
l___private_Lean_Elab_Match_31__elabMatchCore___closed__2 = _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_31__elabMatchCore___closed__2);
l___private_Lean_Elab_Match_31__elabMatchCore___closed__3 = _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_31__elabMatchCore___closed__3);
l___private_Lean_Elab_Match_31__elabMatchCore___closed__4 = _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_31__elabMatchCore___closed__4);
l___private_Lean_Elab_Match_31__elabMatchCore___closed__5 = _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_31__elabMatchCore___closed__5);
l___private_Lean_Elab_Match_31__elabMatchCore___closed__6 = _init_l___private_Lean_Elab_Match_31__elabMatchCore___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_31__elabMatchCore___closed__6);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__1 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__1);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__2);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__3 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__3);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__4);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__5);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__6);
l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7 = _init_l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_32__mkMatchType___main___closed__7);
l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1 = _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__1);
l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__2 = _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__2);
l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__3 = _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__3);
l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__4 = _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__4);
l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__5 = _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__5);
l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__6 = _init_l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_34__mkNewDiscrs___main___closed__6);
l___private_Lean_Elab_Match_35__mkNewPatterns___main___closed__1 = _init_l___private_Lean_Elab_Match_35__mkNewPatterns___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_35__mkNewPatterns___main___closed__1);
l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___closed__1 = _init_l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_38__expandMatchDiscr_x3f___closed__1);
l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Match_39__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
