// Lean compiler output
// Module: Lean.Elab.Binders
// Imports: Init Lean.Elab.Quotation.Precheck Lean.Elab.Term Lean.Parser.Term
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__2;
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__6;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_term_____x5b___x3a___x5d___closed__2;
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__3;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1346____closed__7;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__2(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lean_Elab_Term_expandFunBinders_loop___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__25;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_5248____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letEqnsDecl___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__5;
lean_object* l_Lean_Elab_Term_elabLetDeclAux_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandFun(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__29;
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__2___boxed(lean_object**);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__4;
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letPatDecl___closed__2;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16268____closed__8;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__8;
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__2;
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__4;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3;
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__22;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__18;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__1;
lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__15;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___boxed(lean_object**);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandFun___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_whereDecls_formatter___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_binderTactic___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__5;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__11;
extern lean_object* l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_969____closed__4;
extern lean_object* l_Lean_groupKind___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__14;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__28;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__3;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3;
lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__5;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_6082_(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189_(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__20;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__3;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_autoBoundImplicitLocal___closed__1;
lean_object* l_Lean_Elab_Term_expandFun(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4;
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteNameMk(lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__3;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__10;
lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__24;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__7;
extern lean_object* l_termIfLet___x3a_x3d__Then__Else_____closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let__delayed___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1258____closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__19;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_969____closed__3;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__2(lean_object*);
extern lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5;
lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__3(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
extern lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__26;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteName___closed__2;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Name_instReprName___closed__1;
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_checkBinderAnnotations;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__16;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
extern lean_object* l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1;
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1;
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addTermInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic_match__1(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16268____closed__9;
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__23;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__1;
extern lean_object* l_Lean_Parser_Term_binderDefault___elambda__1___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__1;
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun(lean_object*);
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__6___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__17;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__4;
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__21;
lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_State_fvars___default;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1;
lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__6;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_precheckFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__13;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__27;
extern lean_object* l_Lean_Parser_Term_letRecDecl___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__9;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Syntax_getNumArgs(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_mkHole(x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_ctor_set(x_9, 1, x_14);
x_15 = lean_st_ref_set(x_6, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_1, 4);
lean_dec(x_18);
lean_ctor_set(x_1, 4, x_12);
x_19 = l_Lean_Elab_Term_getMainModule___rarg(x_6, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getCurrMacroScope(x_1, x_2, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Meta_mkArrow___closed__2;
x_26 = l_Lean_addMacroScope(x_20, x_25, x_24);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = l_Lean_Meta_mkArrow___closed__2;
x_30 = l_Lean_addMacroScope(x_20, x_29, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 2);
x_39 = lean_ctor_get(x_1, 5);
x_40 = lean_ctor_get(x_1, 6);
x_41 = lean_ctor_get(x_1, 7);
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_43, 2, x_34);
lean_ctor_set(x_43, 3, x_35);
lean_ctor_set(x_43, 4, x_12);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_43, 6, x_40);
lean_ctor_set(x_43, 7, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*8, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*8 + 1, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*8 + 2, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*8 + 3, x_42);
x_44 = l_Lean_Elab_Term_getMainModule___rarg(x_6, x_16);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Term_getCurrMacroScope(x_43, x_2, x_3, x_4, x_5, x_6, x_46);
lean_dec(x_43);
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
x_51 = l_Lean_Meta_mkArrow___closed__2;
x_52 = l_Lean_addMacroScope(x_45, x_51, x_48);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
x_56 = lean_ctor_get(x_9, 2);
x_57 = lean_ctor_get(x_9, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_55, x_58);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
x_61 = lean_st_ref_set(x_6, x_60, x_10);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_68 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 2);
x_70 = lean_ctor_get(x_1, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 7);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_74 = x_1;
} else {
 lean_dec_ref(x_1);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 8, 4);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_65);
lean_ctor_set(x_75, 3, x_66);
lean_ctor_set(x_75, 4, x_55);
lean_ctor_set(x_75, 5, x_70);
lean_ctor_set(x_75, 6, x_71);
lean_ctor_set(x_75, 7, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*8, x_67);
lean_ctor_set_uint8(x_75, sizeof(void*)*8 + 1, x_68);
lean_ctor_set_uint8(x_75, sizeof(void*)*8 + 2, x_69);
lean_ctor_set_uint8(x_75, sizeof(void*)*8 + 3, x_73);
x_76 = l_Lean_Elab_Term_getMainModule___rarg(x_6, x_62);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Elab_Term_getCurrMacroScope(x_75, x_2, x_3, x_4, x_5, x_6, x_78);
lean_dec(x_75);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Meta_mkArrow___closed__2;
x_84 = l_Lean_addMacroScope(x_77, x_83, x_80);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_mkIdentFrom(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_mkIdentFrom(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inst");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Syntax_isNone(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_st_ref_take(x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_ctor_set(x_14, 1, x_19);
x_20 = lean_st_ref_set(x_7, x_14, x_15);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_2, 4);
lean_dec(x_23);
lean_ctor_set(x_2, 4, x_17);
x_24 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
x_31 = l_Lean_addMacroScope(x_25, x_30, x_29);
x_32 = l_Lean_mkIdentFrom(x_1, x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
x_36 = l_Lean_addMacroScope(x_25, x_35, x_33);
x_37 = l_Lean_mkIdentFrom(x_1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_2, 3);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 2);
x_46 = lean_ctor_get(x_2, 5);
x_47 = lean_ctor_get(x_2, 6);
x_48 = lean_ctor_get(x_2, 7);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_50 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_42);
lean_ctor_set(x_50, 4, x_17);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set(x_50, 7, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*8, x_43);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 1, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 2, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 3, x_49);
x_51 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_21);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_getCurrMacroScope(x_50, x_3, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_50);
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
x_58 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
x_59 = l_Lean_addMacroScope(x_52, x_58, x_55);
x_60 = l_Lean_mkIdentFrom(x_1, x_59);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
x_64 = lean_ctor_get(x_14, 2);
x_65 = lean_ctor_get(x_14, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_63, x_66);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set(x_68, 3, x_65);
x_69 = lean_st_ref_set(x_7, x_68, x_15);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 3);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 2);
x_78 = lean_ctor_get(x_2, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 7);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 x_82 = x_2;
} else {
 lean_dec_ref(x_2);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 8, 4);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_72);
lean_ctor_set(x_83, 2, x_73);
lean_ctor_set(x_83, 3, x_74);
lean_ctor_set(x_83, 4, x_63);
lean_ctor_set(x_83, 5, x_78);
lean_ctor_set(x_83, 6, x_79);
lean_ctor_set(x_83, 7, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*8, x_75);
lean_ctor_set_uint8(x_83, sizeof(void*)*8 + 1, x_76);
lean_ctor_set_uint8(x_83, sizeof(void*)*8 + 2, x_77);
lean_ctor_set_uint8(x_83, sizeof(void*)*8 + 3, x_81);
x_84 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_70);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Term_getCurrMacroScope(x_83, x_3, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_83);
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
x_91 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
x_92 = l_Lean_addMacroScope(x_85, x_91, x_88);
x_93 = l_Lean_mkIdentFrom(x_1, x_92);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_90;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_quoteAutoTactic_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_apply_3(x_3, x_1, x_8, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
x_18 = lean_apply_5(x_2, x_1, x_14, x_15, x_16, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Term_quoteAutoTactic_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_quoteAutoTactic_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array.push");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("push");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, antiquotation is not allowed");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_69; lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_nullKind;
x_78 = lean_name_eq(x_6, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_14 = x_79;
goto block_68;
}
else
{
uint8_t x_80; 
x_80 = l_Lean_Syntax_isAntiquotSuffixSplice(x_1);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Syntax_isAntiquotSplice(x_1);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_14 = x_82;
goto block_68;
}
else
{
lean_object* x_83; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(0);
x_69 = x_83;
goto block_76;
}
}
else
{
lean_object* x_84; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_box(0);
x_69 = x_84;
goto block_76;
}
}
block_68:
{
lean_object* x_15; 
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_11, x_12, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_getMainModule___rarg(x_12, x_23);
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4;
x_28 = lean_name_mk_string(x_2, x_27);
lean_inc(x_28);
x_29 = l_Lean_addMacroScope(x_26, x_28, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Array_empty___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_array_push(x_34, x_5);
x_37 = lean_array_push(x_36, x_16);
x_38 = l_Lean_nullKind___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_35, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_24, 0, x_43);
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4;
x_47 = lean_name_mk_string(x_2, x_46);
lean_inc(x_47);
x_48 = l_Lean_addMacroScope(x_44, x_47, x_22);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_3);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3;
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_50);
x_53 = l_Array_empty___closed__1;
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_array_push(x_53, x_5);
x_56 = lean_array_push(x_55, x_16);
x_57 = l_Lean_nullKind___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_array_push(x_54, x_58);
x_60 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_45);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_76:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_69);
x_70 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6;
x_71 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_1, x_70, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
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
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_9(x_20, lean_box(0), x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = 1;
x_24 = x_2 + x_23;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_24, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_25;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = x_9 < x_8;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_9(x_20, lean_box(0), x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_array_uget(x_7, x_9);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___boxed), 13, 6);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_5);
lean_closure_set(x_24, 3, x_6);
lean_closure_set(x_24, 4, x_10);
lean_closure_set(x_24, 5, x_1);
x_25 = lean_box_usize(x_9);
x_26 = lean_box_usize(x_8);
x_27 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__2___boxed), 17, 9);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_3);
lean_closure_set(x_27, 4, x_4);
lean_closure_set(x_27, 5, x_5);
lean_closure_set(x_27, 6, x_6);
lean_closure_set(x_27, 7, x_7);
lean_closure_set(x_27, 8, x_26);
x_28 = lean_apply_11(x_23, lean_box(0), lean_box(0), x_24, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Binders");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.quoteAutoTactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__1;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__2;
x_3 = lean_unsigned_to_nat(59u);
x_4 = lean_unsigned_to_nat(28u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array.empty");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__6;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("empty");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_term_____x5b___x3a___x5d___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax.node");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__13;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Syntax_addPrec___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__16;
x_2 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
x_2 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAtom");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__25;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, identifier is not allowed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__28;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_10 = l_Lean_Elab_Term_quoteAutoTactic___closed__3;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_7(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = l_Lean_Syntax_isAntiquot(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = l_Lean_Elab_Term_instMonadQuotationTermElabM;
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_quoteAutoTactic___closed__10;
x_31 = l_Lean_addMacroScope(x_28, x_30, x_25);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Term_quoteAutoTactic___closed__8;
x_34 = l_Lean_Elab_Term_quoteAutoTactic___closed__12;
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_array_get_size(x_14);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = 0;
x_39 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_40 = l_Array_term_____x5b___x3a___x5d___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_13, x_39, x_20, x_40, x_32, x_32, x_14, x_37, x_38, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_49);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_54 = l_Lean_addMacroScope(x_52, x_53, x_48);
x_55 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_56 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_56);
x_58 = l_Array_empty___closed__1;
x_59 = lean_array_push(x_58, x_57);
lean_inc(x_13);
x_60 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_32, x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = l___private_Init_Meta_0__Lean_quoteNameMk(x_13);
x_62 = lean_array_push(x_58, x_61);
x_63 = lean_array_push(x_62, x_42);
x_64 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_63);
lean_ctor_set(x_1, 0, x_64);
x_65 = lean_array_push(x_59, x_1);
x_66 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_50, 0, x_67);
return x_50;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_13);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
lean_dec(x_60);
x_69 = l_Lean_Name_toString___closed__1;
x_70 = l_String_intercalate(x_69, x_68);
x_71 = l_Lean_Name_instReprName___closed__1;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l_Lean_nameLitKind;
x_74 = lean_box(2);
x_75 = l_Lean_Syntax_mkLit(x_73, x_72, x_74);
x_76 = l_Lean_mkOptionalNode___closed__2;
x_77 = lean_array_push(x_76, x_75);
x_78 = l_Lean_instQuoteName___closed__2;
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_78);
x_79 = lean_array_push(x_58, x_1);
x_80 = lean_array_push(x_79, x_42);
x_81 = l_Lean_nullKind___closed__2;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_array_push(x_59, x_82);
x_84 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_50, 0, x_85);
return x_50;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_50, 0);
x_87 = lean_ctor_get(x_50, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_50);
x_88 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_89 = l_Lean_addMacroScope(x_86, x_88, x_48);
x_90 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_91 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_92 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_92, 0, x_45);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_91);
x_93 = l_Array_empty___closed__1;
x_94 = lean_array_push(x_93, x_92);
lean_inc(x_13);
x_95 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_32, x_13);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = l___private_Init_Meta_0__Lean_quoteNameMk(x_13);
x_97 = lean_array_push(x_93, x_96);
x_98 = lean_array_push(x_97, x_42);
x_99 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_98);
lean_ctor_set(x_1, 0, x_99);
x_100 = lean_array_push(x_94, x_1);
x_101 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_87);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_13);
x_104 = lean_ctor_get(x_95, 0);
lean_inc(x_104);
lean_dec(x_95);
x_105 = l_Lean_Name_toString___closed__1;
x_106 = l_String_intercalate(x_105, x_104);
x_107 = l_Lean_Name_instReprName___closed__1;
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = l_Lean_nameLitKind;
x_110 = lean_box(2);
x_111 = l_Lean_Syntax_mkLit(x_109, x_108, x_110);
x_112 = l_Lean_mkOptionalNode___closed__2;
x_113 = lean_array_push(x_112, x_111);
x_114 = l_Lean_instQuoteName___closed__2;
lean_ctor_set(x_1, 1, x_113);
lean_ctor_set(x_1, 0, x_114);
x_115 = lean_array_push(x_93, x_1);
x_116 = lean_array_push(x_115, x_42);
x_117 = l_Lean_nullKind___closed__2;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_94, x_118);
x_120 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_87);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_41);
if (x_123 == 0)
{
return x_41;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_41, 0);
x_125 = lean_ctor_get(x_41, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_41);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_1);
x_127 = l_Lean_Elab_Term_instMonadQuotationTermElabM;
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_8);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Elab_Term_quoteAutoTactic___closed__10;
x_139 = l_Lean_addMacroScope(x_136, x_138, x_133);
x_140 = lean_box(0);
x_141 = l_Lean_Elab_Term_quoteAutoTactic___closed__8;
x_142 = l_Lean_Elab_Term_quoteAutoTactic___closed__12;
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_130);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_139);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_array_get_size(x_14);
x_145 = lean_usize_of_nat(x_144);
lean_dec(x_144);
x_146 = 0;
x_147 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_148 = l_Array_term_____x5b___x3a___x5d___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_149 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_13, x_147, x_128, x_148, x_140, x_140, x_14, x_145, x_146, x_143, x_2, x_3, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_154);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_157);
lean_dec(x_7);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_163 = l_Lean_addMacroScope(x_159, x_162, x_156);
x_164 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_165 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_166 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 2, x_163);
lean_ctor_set(x_166, 3, x_165);
x_167 = l_Array_empty___closed__1;
x_168 = lean_array_push(x_167, x_166);
lean_inc(x_13);
x_169 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_140, x_13);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_170 = l___private_Init_Meta_0__Lean_quoteNameMk(x_13);
x_171 = lean_array_push(x_167, x_170);
x_172 = lean_array_push(x_171, x_150);
x_173 = l_Lean_nullKind___closed__2;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_array_push(x_168, x_174);
x_176 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
if (lean_is_scalar(x_161)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_161;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_160);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_13);
x_179 = lean_ctor_get(x_169, 0);
lean_inc(x_179);
lean_dec(x_169);
x_180 = l_Lean_Name_toString___closed__1;
x_181 = l_String_intercalate(x_180, x_179);
x_182 = l_Lean_Name_instReprName___closed__1;
x_183 = lean_string_append(x_182, x_181);
lean_dec(x_181);
x_184 = l_Lean_nameLitKind;
x_185 = lean_box(2);
x_186 = l_Lean_Syntax_mkLit(x_184, x_183, x_185);
x_187 = l_Lean_mkOptionalNode___closed__2;
x_188 = lean_array_push(x_187, x_186);
x_189 = l_Lean_instQuoteName___closed__2;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_array_push(x_167, x_190);
x_192 = lean_array_push(x_191, x_150);
x_193 = l_Lean_nullKind___closed__2;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_array_push(x_168, x_194);
x_196 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
if (lean_is_scalar(x_161)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_161;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_160);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_149, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_149, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_201 = x_149;
} else {
 lean_dec_ref(x_149);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_14);
lean_dec(x_13);
x_203 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6;
x_204 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__4(x_1, x_203, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_204;
}
}
case 2:
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_1);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_206 = lean_ctor_get(x_1, 1);
x_207 = lean_ctor_get(x_1, 0);
lean_dec(x_207);
x_208 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_8);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_210);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_213);
lean_dec(x_7);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = l_Lean_Elab_Term_quoteAutoTactic___closed__24;
x_218 = l_Lean_addMacroScope(x_216, x_217, x_212);
x_219 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_220 = l_Lean_Elab_Term_quoteAutoTactic___closed__27;
x_221 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_221, 0, x_209);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set(x_221, 2, x_218);
lean_ctor_set(x_221, 3, x_220);
x_222 = l_Array_empty___closed__1;
x_223 = lean_array_push(x_222, x_221);
x_224 = lean_box(2);
x_225 = l_Lean_Syntax_mkStrLit(x_206, x_224);
lean_dec(x_206);
x_226 = lean_array_push(x_222, x_225);
x_227 = l_Lean_nullKind___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_226);
lean_ctor_set(x_1, 0, x_227);
x_228 = lean_array_push(x_223, x_1);
x_229 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
lean_ctor_set(x_214, 0, x_230);
return x_214;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_231 = lean_ctor_get(x_214, 0);
x_232 = lean_ctor_get(x_214, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_214);
x_233 = l_Lean_Elab_Term_quoteAutoTactic___closed__24;
x_234 = l_Lean_addMacroScope(x_231, x_233, x_212);
x_235 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_236 = l_Lean_Elab_Term_quoteAutoTactic___closed__27;
x_237 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_237, 0, x_209);
lean_ctor_set(x_237, 1, x_235);
lean_ctor_set(x_237, 2, x_234);
lean_ctor_set(x_237, 3, x_236);
x_238 = l_Array_empty___closed__1;
x_239 = lean_array_push(x_238, x_237);
x_240 = lean_box(2);
x_241 = l_Lean_Syntax_mkStrLit(x_206, x_240);
lean_dec(x_206);
x_242 = lean_array_push(x_238, x_241);
x_243 = l_Lean_nullKind___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_243);
x_244 = lean_array_push(x_239, x_1);
x_245 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_232);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_248 = lean_ctor_get(x_1, 1);
lean_inc(x_248);
lean_dec(x_1);
x_249 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_8);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_251);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_254);
lean_dec(x_7);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
x_259 = l_Lean_Elab_Term_quoteAutoTactic___closed__24;
x_260 = l_Lean_addMacroScope(x_256, x_259, x_253);
x_261 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_262 = l_Lean_Elab_Term_quoteAutoTactic___closed__27;
x_263 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_263, 0, x_250);
lean_ctor_set(x_263, 1, x_261);
lean_ctor_set(x_263, 2, x_260);
lean_ctor_set(x_263, 3, x_262);
x_264 = l_Array_empty___closed__1;
x_265 = lean_array_push(x_264, x_263);
x_266 = lean_box(2);
x_267 = l_Lean_Syntax_mkStrLit(x_248, x_266);
lean_dec(x_248);
x_268 = lean_array_push(x_264, x_267);
x_269 = l_Lean_nullKind___closed__2;
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_array_push(x_265, x_270);
x_272 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
if (lean_is_scalar(x_258)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_258;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_257);
return x_274;
}
}
default: 
{
lean_object* x_275; lean_object* x_276; 
x_275 = l_Lean_Elab_Term_quoteAutoTactic___closed__29;
x_276 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__4(x_1, x_275, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_276;
}
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__2___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__2(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_auto");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareTacticSyntax___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1258____closed__1;
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_ctor_set(x_10, 1, x_15);
x_16 = lean_st_ref_set(x_7, x_10, x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 4);
lean_dec(x_19);
lean_ctor_set(x_2, 4, x_13);
x_20 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_27 = l_Lean_addMacroScope(x_21, x_26, x_24);
x_28 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_declareTacticSyntax___closed__4;
x_33 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Elab_Term_elabTerm(x_30, x_32, x_33, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Meta_instantiateMVars(x_35, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_63 = lean_st_ref_get(x_7, x_39);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_40 = x_67;
goto block_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = l_Lean_Elab_Term_declareTacticSyntax___closed__5;
x_70 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_40 = x_73;
goto block_62;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
lean_inc(x_38);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_38);
x_76 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_69, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_40 = x_77;
goto block_62;
}
}
block_62:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_inc(x_27);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_box(0);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_inc(x_6);
lean_inc(x_2);
x_47 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_27);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
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
lean_dec(x_46);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_37);
if (x_78 == 0)
{
return x_37;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_37, 0);
x_80 = lean_ctor_get(x_37, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_37);
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
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_34);
if (x_82 == 0)
{
return x_34;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_34, 0);
x_84 = lean_ctor_get(x_34, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_34);
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
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_29);
if (x_86 == 0)
{
return x_29;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_29, 0);
x_88 = lean_ctor_get(x_29, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_29);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_90 = lean_ctor_get(x_2, 0);
x_91 = lean_ctor_get(x_2, 1);
x_92 = lean_ctor_get(x_2, 2);
x_93 = lean_ctor_get(x_2, 3);
x_94 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_95 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_96 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 2);
x_97 = lean_ctor_get(x_2, 5);
x_98 = lean_ctor_get(x_2, 6);
x_99 = lean_ctor_get(x_2, 7);
x_100 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 3);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_2);
x_101 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_91);
lean_ctor_set(x_101, 2, x_92);
lean_ctor_set(x_101, 3, x_93);
lean_ctor_set(x_101, 4, x_13);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_101, 6, x_98);
lean_ctor_set(x_101, 7, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*8, x_94);
lean_ctor_set_uint8(x_101, sizeof(void*)*8 + 1, x_95);
lean_ctor_set_uint8(x_101, sizeof(void*)*8 + 2, x_96);
lean_ctor_set_uint8(x_101, sizeof(void*)*8 + 3, x_100);
x_102 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_17);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Elab_Term_getCurrMacroScope(x_101, x_3, x_4, x_5, x_6, x_7, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_109 = l_Lean_addMacroScope(x_103, x_108, x_106);
x_110 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_101);
x_111 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_101, x_3, x_4, x_5, x_6, x_7, x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Elab_Term_declareTacticSyntax___closed__4;
x_115 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_101);
x_116 = l_Lean_Elab_Term_elabTerm(x_112, x_114, x_115, x_115, x_101, x_3, x_4, x_5, x_6, x_7, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_119 = l_Lean_Meta_instantiateMVars(x_117, x_4, x_5, x_6, x_7, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_144 = lean_st_ref_get(x_7, x_121);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 3);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_ctor_get_uint8(x_146, sizeof(void*)*1);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_122 = x_148;
goto block_143;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
lean_dec(x_144);
x_150 = l_Lean_Elab_Term_declareTacticSyntax___closed__5;
x_151 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_150, x_101, x_3, x_4, x_5, x_6, x_7, x_149);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_122 = x_154;
goto block_143;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
lean_dec(x_151);
lean_inc(x_120);
x_156 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_156, 0, x_120);
x_157 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_150, x_156, x_101, x_3, x_4, x_5, x_6, x_7, x_155);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_122 = x_158;
goto block_143;
}
}
block_143:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_inc(x_109);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_110);
lean_ctor_set(x_124, 2, x_123);
x_125 = lean_box(0);
x_126 = 1;
x_127 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_120);
lean_ctor_set(x_127, 2, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*3, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
lean_inc(x_6);
lean_inc(x_101);
x_129 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_128, x_101, x_3, x_4, x_5, x_6, x_7, x_122);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_128, x_101, x_3, x_4, x_5, x_6, x_7, x_130);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_109);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_109);
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
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
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_128);
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_ctor_get(x_129, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_141 = x_129;
} else {
 lean_dec_ref(x_129);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_159 = lean_ctor_get(x_119, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_119, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_161 = x_119;
} else {
 lean_dec_ref(x_119);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = lean_ctor_get(x_116, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_116, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_165 = x_116;
} else {
 lean_dec_ref(x_116);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_167 = lean_ctor_get(x_111, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_111, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_169 = x_111;
} else {
 lean_dec_ref(x_111);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_171 = lean_ctor_get(x_10, 0);
x_172 = lean_ctor_get(x_10, 1);
x_173 = lean_ctor_get(x_10, 2);
x_174 = lean_ctor_get(x_10, 3);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_10);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_172, x_175);
x_177 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_173);
lean_ctor_set(x_177, 3, x_174);
x_178 = lean_st_ref_set(x_7, x_177, x_11);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_ctor_get(x_2, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_2, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_2, 3);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_185 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_186 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 2);
x_187 = lean_ctor_get(x_2, 5);
lean_inc(x_187);
x_188 = lean_ctor_get(x_2, 6);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 7);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 x_191 = x_2;
} else {
 lean_dec_ref(x_2);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 8, 4);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_181);
lean_ctor_set(x_192, 2, x_182);
lean_ctor_set(x_192, 3, x_183);
lean_ctor_set(x_192, 4, x_172);
lean_ctor_set(x_192, 5, x_187);
lean_ctor_set(x_192, 6, x_188);
lean_ctor_set(x_192, 7, x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*8, x_184);
lean_ctor_set_uint8(x_192, sizeof(void*)*8 + 1, x_185);
lean_ctor_set_uint8(x_192, sizeof(void*)*8 + 2, x_186);
lean_ctor_set_uint8(x_192, sizeof(void*)*8 + 3, x_190);
x_193 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_179);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Elab_Term_getCurrMacroScope(x_192, x_3, x_4, x_5, x_6, x_7, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_200 = l_Lean_addMacroScope(x_194, x_199, x_197);
x_201 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_192);
x_202 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_192, x_3, x_4, x_5, x_6, x_7, x_198);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l_Lean_Elab_Term_declareTacticSyntax___closed__4;
x_206 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_192);
x_207 = l_Lean_Elab_Term_elabTerm(x_203, x_205, x_206, x_206, x_192, x_3, x_4, x_5, x_6, x_7, x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_210 = l_Lean_Meta_instantiateMVars(x_208, x_4, x_5, x_6, x_7, x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_235 = lean_st_ref_get(x_7, x_212);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 3);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_ctor_get_uint8(x_237, sizeof(void*)*1);
lean_dec(x_237);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
lean_dec(x_235);
x_213 = x_239;
goto block_234;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_235, 1);
lean_inc(x_240);
lean_dec(x_235);
x_241 = l_Lean_Elab_Term_declareTacticSyntax___closed__5;
x_242 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_241, x_192, x_3, x_4, x_5, x_6, x_7, x_240);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_213 = x_245;
goto block_234;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
lean_inc(x_211);
x_247 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_247, 0, x_211);
x_248 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_241, x_247, x_192, x_3, x_4, x_5, x_6, x_7, x_246);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_213 = x_249;
goto block_234;
}
}
block_234:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_inc(x_200);
x_215 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_215, 0, x_200);
lean_ctor_set(x_215, 1, x_201);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_box(0);
x_217 = 1;
x_218 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_211);
lean_ctor_set(x_218, 2, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*3, x_217);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
lean_inc(x_6);
lean_inc(x_192);
x_220 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_219, x_192, x_3, x_4, x_5, x_6, x_7, x_213);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_219, x_192, x_3, x_4, x_5, x_6, x_7, x_221);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_200);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_200);
x_226 = lean_ctor_get(x_222, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_228 = x_222;
} else {
 lean_dec_ref(x_222);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_219);
lean_dec(x_200);
lean_dec(x_192);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_230 = lean_ctor_get(x_220, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_220, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_232 = x_220;
} else {
 lean_dec_ref(x_220);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_200);
lean_dec(x_192);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_250 = lean_ctor_get(x_210, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_210, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_252 = x_210;
} else {
 lean_dec_ref(x_210);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_200);
lean_dec(x_192);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_254 = lean_ctor_get(x_207, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_207, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_256 = x_207;
} else {
 lean_dec_ref(x_207);
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
lean_dec(x_200);
lean_dec(x_192);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = lean_ctor_get(x_202, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_202, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_260 = x_202;
} else {
 lean_dec_ref(x_202);
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
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Syntax_isNone(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
lean_inc(x_12);
x_13 = l_Lean_Syntax_getKind(x_12);
x_14 = l_Lean_Parser_Term_binderDefault___elambda__1___closed__2;
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Parser_Term_binderTactic___elambda__1___closed__2;
x_17 = lean_name_eq(x_13, x_16);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__6___rarg(x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_12, x_19);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_20);
x_21 = l_Lean_Elab_Term_declareTacticSyntax(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_29);
lean_dec(x_8);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_34 = l_Lean_addMacroScope(x_32, x_33, x_28);
x_35 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2;
x_36 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4;
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Array_empty___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_array_push(x_38, x_1);
x_41 = l_Lean_mkIdentFrom(x_20, x_22);
lean_dec(x_20);
x_42 = lean_array_push(x_40, x_41);
x_43 = l_Lean_nullKind___closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_push(x_39, x_44);
x_46 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_30, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_48 = lean_ctor_get(x_30, 0);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_30);
x_50 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_51 = l_Lean_addMacroScope(x_48, x_50, x_28);
x_52 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2;
x_53 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4;
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_25);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_53);
x_55 = l_Array_empty___closed__1;
x_56 = lean_array_push(x_55, x_54);
x_57 = lean_array_push(x_55, x_1);
x_58 = l_Lean_mkIdentFrom(x_20, x_22);
lean_dec(x_20);
x_59 = lean_array_push(x_57, x_58);
x_60 = l_Lean_nullKind___closed__2;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_array_push(x_56, x_61);
x_63 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_49);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_21);
if (x_66 == 0)
{
return x_21;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_21, 0);
x_68 = lean_ctor_get(x_21, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_21);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_13);
x_70 = lean_unsigned_to_nat(1u);
x_71 = l_Lean_Syntax_getArg(x_12, x_70);
lean_dec(x_12);
x_72 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_9);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_77);
lean_dec(x_8);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_82 = l_Lean_addMacroScope(x_80, x_81, x_76);
x_83 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
x_84 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8;
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_84);
x_86 = l_Array_empty___closed__1;
x_87 = lean_array_push(x_86, x_85);
x_88 = lean_array_push(x_86, x_1);
x_89 = lean_array_push(x_88, x_71);
x_90 = l_Lean_nullKind___closed__2;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_array_push(x_87, x_91);
x_93 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_78, 0, x_94);
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
x_97 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_98 = l_Lean_addMacroScope(x_95, x_97, x_76);
x_99 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
x_100 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8;
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_73);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
x_102 = l_Array_empty___closed__1;
x_103 = lean_array_push(x_102, x_101);
x_104 = lean_array_push(x_102, x_1);
x_105 = lean_array_push(x_104, x_71);
x_106 = l_Lean_nullKind___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_103, x_107);
x_109 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_96);
return x_111;
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_9);
return x_112;
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier or `_` expected");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_4);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
lean_inc(x_17);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Lean_identKind;
x_20 = lean_name_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
x_22 = lean_name_eq(x_18, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2;
x_24 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__4(x_17, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
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
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 1;
x_30 = x_2 + x_29;
x_31 = x_17;
x_32 = lean_array_uset(x_16, x_2, x_31);
x_2 = x_30;
x_3 = x_32;
goto _start;
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
x_34 = 1;
x_35 = x_2 + x_34;
x_36 = x_17;
x_37 = lean_array_uset(x_16, x_2, x_36);
x_2 = x_35;
x_3 = x_37;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Lean_Syntax_getArgs(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = x_9;
x_13 = lean_box_usize(x_11);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___boxed), 10, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_12);
x_16 = x_15;
x_17 = lean_apply_7(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_expandOptType(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isNone(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_mkHole(x_1);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandOptType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = x_15;
lean_inc(x_5);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = 1;
x_25 = x_3 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_17, x_3, x_26);
x_3 = x_25;
x_4 = x_27;
x_11 = x_21;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = x_15;
lean_inc(x_5);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = 1;
x_25 = x_3 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_17, x_3, x_26);
x_3 = x_25;
x_4 = x_27;
x_11 = x_21;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = x_15;
lean_inc(x_5);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = 1;
x_25 = x_3 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_17, x_3, x_26);
x_3 = x_25;
x_4 = x_27;
x_11 = x_21;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_9 = l_Lean_Syntax_getKind(x_1);
x_10 = l_Lean_expandExplicitBindersAux_loop___closed__2;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_13 = lean_name_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_15 = lean_name_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_17 = lean_name_eq(x_9, x_16);
lean_dec(x_9);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
x_28 = l_Lean_mkOptionalNode___closed__2;
x_29 = lean_array_push(x_28, x_27);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
lean_dec(x_1);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_34);
x_36 = l_Lean_mkOptionalNode___closed__2;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(2u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
x_46 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_45);
lean_dec(x_45);
lean_dec(x_1);
x_47 = lean_array_get_size(x_42);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = x_42;
x_50 = lean_box_usize(x_48);
x_51 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_52 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed), 11, 4);
lean_closure_set(x_52, 0, x_46);
lean_closure_set(x_52, 1, x_50);
lean_closure_set(x_52, 2, x_51);
lean_closure_set(x_52, 3, x_49);
x_53 = x_52;
x_54 = lean_apply_7(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_9);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unsigned_to_nat(2u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
x_66 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_65);
lean_dec(x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = l_Lean_Syntax_getArg(x_1, x_67);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_69 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(x_66, x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_array_get_size(x_62);
x_73 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_74 = x_62;
x_75 = lean_box_usize(x_73);
x_76 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_77 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed), 11, 4);
lean_closure_set(x_77, 0, x_70);
lean_closure_set(x_77, 1, x_75);
lean_closure_set(x_77, 2, x_76);
lean_closure_set(x_77, 3, x_74);
x_78 = x_77;
x_79 = lean_apply_7(x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_71);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_62);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_69);
if (x_80 == 0)
{
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
return x_61;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_61, 0);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_61);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_9);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Syntax_getArg(x_1, x_88);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_90 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unsigned_to_nat(1u);
x_94 = l_Lean_Syntax_getArg(x_1, x_93);
x_95 = l_Lean_Elab_Term_expandOptType(x_1, x_94);
lean_dec(x_94);
lean_dec(x_1);
x_96 = lean_array_get_size(x_91);
x_97 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_98 = x_91;
x_99 = lean_box_usize(x_97);
x_100 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_101 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed), 11, 4);
lean_closure_set(x_101, 0, x_95);
lean_closure_set(x_101, 1, x_99);
lean_closure_set(x_101, 2, x_100);
lean_closure_set(x_101, 3, x_98);
x_102 = x_101;
x_103 = lean_apply_7(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_92);
return x_103;
}
else
{
uint8_t x_104; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_90);
if (x_104 == 0)
{
return x_90;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_90, 0);
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_90);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to infer binder type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3;
x_11 = l_Lean_Elab_Term_registerCustomErrorIfMVar(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Std_PersistentArray_empty___closed__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addTermInfo___spec__2(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_28;
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid binder name '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', it must be atomic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Syntax_getId(x_9);
x_11 = lean_erase_macro_scopes(x_10);
x_12 = l_Lean_Name_isAtomic(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(x_9, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkBinderAnnotations");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("check whether type is a class instance whenever the binder annotation `[...]` is used");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__2;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_9);
lean_inc(x_6);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
x_18 = lean_array_push(x_3, x_6);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_4, x_5, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getId(x_15);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed), 13, 5);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
x_19 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_16, x_17, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid binder annotation, type is not a class instance");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nuse the command `set_option checkBinderAnnotations false` to disable the check");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_3);
lean_inc(x_9);
lean_inc(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_19 = l_Lean_Elab_Term_elabType(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_18);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_20, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_26 = l_Lean_BinderInfo_isInstImplicit(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(x_15, x_3, x_4, x_1, x_2, x_20, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Elab_Term_checkBinderAnnotations;
x_30 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_24, x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(x_15, x_3, x_4, x_1, x_2, x_20, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_32;
}
else
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_33 = l_Lean_Meta_isClass_x3f(x_20, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_indentExpr(x_20);
x_37 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_18, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_18);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_18);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_box(0);
x_48 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(x_15, x_3, x_4, x_1, x_2, x_20, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_15);
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
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
return x_33;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
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
lean_dec(x_18);
lean_dec(x_15);
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
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
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
lean_dec(x_15);
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
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
return x_16;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_16, 0);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_1, x_3, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed), 11, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_17, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Meta_getResetPostponed(x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 0;
x_22 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Meta_processPostponed(x_21, x_22, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_setPostponed(x_16, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(x_16, x_19, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_10 = x_38;
x_11 = x_39;
goto block_14;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
x_40 = lean_ctor_get(x_23, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = l_Lean_Meta_setPostponed(x_16, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_dec(x_18);
x_49 = l_Lean_Meta_setPostponed(x_16, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = l_Array_empty___closed__1;
x_13 = lean_apply_1(x_2, x_12);
x_14 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_2, x_11);
x_13 = lean_apply_8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_mkOptionalNode___closed__2;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabBinder___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Term_elabType(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_2, x_11, x_13, x_14, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
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
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 9, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = l_Lean_Elab_Term_elabBinders___rarg(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__6___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_inc(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_empty___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_prec_x28___x29___closed__3;
lean_inc(x_17);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_27, x_30);
x_32 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_969____closed__4;
x_33 = l_Lean_addMacroScope(x_24, x_32, x_20);
x_34 = lean_box(0);
x_35 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_969____closed__3;
lean_inc(x_17);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
x_37 = lean_array_push(x_27, x_36);
x_38 = l_Lean_nullKind___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_31, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_16268____closed__9;
lean_inc(x_17);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_27, x_42);
x_44 = lean_array_push(x_43, x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_40, x_45);
x_47 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_48 = lean_array_push(x_46, x_47);
x_49 = l_prec_x28___x29___closed__7;
lean_inc(x_17);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_push(x_48, x_50);
x_52 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_array_push(x_27, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_push(x_28, x_55);
x_57 = l_myMacro____x40_Init_Notation___hyg_1346____closed__7;
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_17);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_push(x_56, x_58);
x_60 = lean_array_push(x_59, x_15);
x_61 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_22, 0, x_62);
return x_22;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_63 = lean_ctor_get(x_22, 0);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_22);
x_65 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_inc(x_17);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Array_empty___closed__1;
x_68 = lean_array_push(x_67, x_66);
x_69 = l_prec_x28___x29___closed__3;
lean_inc(x_17);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_17);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_67, x_70);
x_72 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_969____closed__4;
x_73 = l_Lean_addMacroScope(x_63, x_72, x_20);
x_74 = lean_box(0);
x_75 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_969____closed__3;
lean_inc(x_17);
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_17);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_74);
x_77 = lean_array_push(x_67, x_76);
x_78 = l_Lean_nullKind___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_push(x_71, x_79);
x_81 = l_myMacro____x40_Init_Notation___hyg_16268____closed__9;
lean_inc(x_17);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_17);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_push(x_67, x_82);
x_84 = lean_array_push(x_83, x_13);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_push(x_80, x_85);
x_87 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_88 = lean_array_push(x_86, x_87);
x_89 = l_prec_x28___x29___closed__7;
lean_inc(x_17);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_push(x_88, x_90);
x_92 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_67, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_78);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_68, x_95);
x_97 = l_myMacro____x40_Init_Notation___hyg_1346____closed__7;
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_17);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_push(x_96, x_98);
x_100 = lean_array_push(x_99, x_15);
x_101 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_64);
return x_103;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabArrow___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabArrow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_mkOptionalNode___closed__2;
x_15 = lean_array_push(x_14, x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 9, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = l_Lean_Elab_Term_elabBinders___rarg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabDepArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_mkArrow___closed__2;
x_9 = l_Lean_addMacroScope(x_7, x_8, x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_mkArrow___closed__2;
x_19 = l_Lean_addMacroScope(x_17, x_18, x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__2(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_mkIdentFrom(x_1, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = l_Lean_mkIdentFrom(x_1, x_15);
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(1, 1, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_18; 
x_18 = x_4 < x_3;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_array_uget(x_2, x_4);
x_22 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
lean_inc(x_1);
x_23 = lean_name_mk_string(x_1, x_22);
lean_inc(x_21);
x_24 = l_Lean_Syntax_isOfKind(x_21, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_identKind___closed__2;
lean_inc(x_21);
x_26 = l_Lean_Syntax_isOfKind(x_21, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_box(0);
x_8 = x_27;
x_9 = x_7;
goto block_17;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_8 = x_28;
x_9 = x_7;
goto block_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_6);
x_29 = l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(x_21, x_6, x_7);
lean_dec(x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
x_8 = x_30;
x_9 = x_31;
goto block_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_8 = x_34;
x_9 = x_31;
goto block_17;
}
}
}
block_17:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_array_push(x_5, x_12);
x_14 = 1;
x_15 = x_4 + x_14;
x_4 = x_15;
x_5 = x_13;
x_7 = x_9;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_19 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
lean_inc(x_1);
x_20 = l_Lean_Syntax_isOfKind(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
lean_inc(x_1);
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_23 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_24 = l_Lean_Syntax_isOfKind(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_box(0);
x_4 = x_25;
x_5 = x_3;
goto block_18;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_4 = x_26;
x_5 = x_3;
goto block_18;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
x_4 = x_28;
x_5 = x_29;
goto block_18;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_4 = x_32;
x_5 = x_29;
goto block_18;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_68; uint8_t x_69; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
lean_dec(x_1);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_68 = l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
lean_inc(x_34);
x_69 = l_Lean_Syntax_isOfKind(x_34, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_identKind___closed__2;
lean_inc(x_34);
x_71 = l_Lean_Syntax_isOfKind(x_34, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_34);
x_72 = lean_box(0);
x_38 = x_72;
x_39 = x_3;
goto block_67;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_34);
x_38 = x_73;
x_39 = x_3;
goto block_67;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_inc(x_2);
x_74 = l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(x_34, x_2, x_3);
lean_dec(x_34);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
x_38 = x_75;
x_39 = x_76;
goto block_67;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_38 = x_79;
x_39 = x_76;
goto block_67;
}
}
block_67:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Array_empty___closed__1;
x_44 = lean_array_push(x_43, x_42);
x_45 = lean_array_get_size(x_37);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
x_49 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3(x_48, x_37, x_46, x_47, x_44, x_2, x_39);
lean_dec(x_37);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_49, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_49, 0, x_61);
return x_49;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_dec(x_49);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
}
}
block_18:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Array_empty___closed__1;
x_11 = lean_array_push(x_10, x_9);
lean_ctor_set(x_4, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Array_empty___closed__1;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
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
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get_usize(x_10, 2);
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get_usize(x_11, 2);
x_23 = lean_ctor_get(x_11, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get_usize(x_12, 2);
x_27 = lean_ctor_get(x_12, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 1);
x_30 = lean_ctor_get_usize(x_13, 2);
x_31 = lean_ctor_get(x_13, 0);
lean_dec(x_31);
x_32 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_33 = lean_string_dec_eq(x_29, x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_object* x_34; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_dec(x_25);
lean_free_object(x_11);
lean_dec(x_21);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_apply_1(x_9, x_1);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_1, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_1, 0);
lean_dec(x_37);
x_38 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_39 = lean_string_dec_eq(x_25, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_13, 1, x_32);
x_40 = lean_apply_1(x_9, x_1);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_25);
x_41 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_42 = lean_string_dec_eq(x_21, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_12, 1, x_38);
x_43 = lean_apply_1(x_9, x_1);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_21);
x_44 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_45 = lean_string_dec_eq(x_17, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_2);
x_46 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_47 = lean_string_dec_eq(x_17, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_3);
x_48 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_49 = lean_string_dec_eq(x_17, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_4);
x_50 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_51 = lean_string_dec_eq(x_17, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_5);
x_52 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_53 = lean_string_dec_eq(x_17, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_6);
x_54 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_55 = lean_string_dec_eq(x_17, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_7);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_11, 1, x_41);
x_56 = lean_apply_1(x_9, x_1);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_1);
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
x_57 = lean_box_usize(x_30);
x_58 = lean_box_usize(x_26);
x_59 = lean_box_usize(x_22);
x_60 = lean_box_usize(x_18);
x_61 = lean_apply_5(x_7, x_15, x_57, x_58, x_59, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_1);
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
x_62 = lean_box_usize(x_30);
x_63 = lean_box_usize(x_26);
x_64 = lean_box_usize(x_22);
x_65 = lean_box_usize(x_18);
x_66 = lean_apply_5(x_6, x_15, x_62, x_63, x_64, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_1);
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_box_usize(x_30);
x_68 = lean_box_usize(x_26);
x_69 = lean_box_usize(x_22);
x_70 = lean_box_usize(x_18);
x_71 = lean_apply_5(x_5, x_15, x_67, x_68, x_69, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_1);
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_box_usize(x_30);
x_73 = lean_box_usize(x_26);
x_74 = lean_box_usize(x_22);
x_75 = lean_box_usize(x_18);
x_76 = lean_apply_5(x_4, x_15, x_72, x_73, x_74, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_1);
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = lean_box_usize(x_30);
x_78 = lean_box_usize(x_26);
x_79 = lean_box_usize(x_22);
x_80 = lean_box_usize(x_18);
x_81 = lean_apply_5(x_3, x_15, x_77, x_78, x_79, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_1);
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_box_usize(x_30);
x_83 = lean_box_usize(x_26);
x_84 = lean_box_usize(x_22);
x_85 = lean_box_usize(x_18);
x_86 = lean_apply_5(x_2, x_15, x_82, x_83, x_84, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_1);
x_87 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_88 = lean_string_dec_eq(x_25, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_13, 1, x_32);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_15);
x_90 = lean_apply_1(x_9, x_89);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_25);
x_91 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_92 = lean_string_dec_eq(x_21, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_12, 1, x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_15);
x_94 = lean_apply_1(x_9, x_93);
return x_94;
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_dec(x_21);
x_95 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_96 = lean_string_dec_eq(x_17, x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_2);
x_97 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_98 = lean_string_dec_eq(x_17, x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_3);
x_99 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_100 = lean_string_dec_eq(x_17, x_99);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_4);
x_101 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_102 = lean_string_dec_eq(x_17, x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
lean_dec(x_5);
x_103 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_104 = lean_string_dec_eq(x_17, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_6);
x_105 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_106 = lean_string_dec_eq(x_17, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_7);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_12, 1, x_87);
lean_ctor_set(x_11, 1, x_91);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_10);
lean_ctor_set(x_107, 1, x_15);
x_108 = lean_apply_1(x_9, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
x_109 = lean_box_usize(x_30);
x_110 = lean_box_usize(x_26);
x_111 = lean_box_usize(x_22);
x_112 = lean_box_usize(x_18);
x_113 = lean_apply_5(x_7, x_15, x_109, x_110, x_111, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
x_114 = lean_box_usize(x_30);
x_115 = lean_box_usize(x_26);
x_116 = lean_box_usize(x_22);
x_117 = lean_box_usize(x_18);
x_118 = lean_apply_5(x_6, x_15, x_114, x_115, x_116, x_117);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_119 = lean_box_usize(x_30);
x_120 = lean_box_usize(x_26);
x_121 = lean_box_usize(x_22);
x_122 = lean_box_usize(x_18);
x_123 = lean_apply_5(x_5, x_15, x_119, x_120, x_121, x_122);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_124 = lean_box_usize(x_30);
x_125 = lean_box_usize(x_26);
x_126 = lean_box_usize(x_22);
x_127 = lean_box_usize(x_18);
x_128 = lean_apply_5(x_4, x_15, x_124, x_125, x_126, x_127);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_129 = lean_box_usize(x_30);
x_130 = lean_box_usize(x_26);
x_131 = lean_box_usize(x_22);
x_132 = lean_box_usize(x_18);
x_133 = lean_apply_5(x_3, x_15, x_129, x_130, x_131, x_132);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_free_object(x_13);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_box_usize(x_30);
x_135 = lean_box_usize(x_26);
x_136 = lean_box_usize(x_22);
x_137 = lean_box_usize(x_18);
x_138 = lean_apply_5(x_2, x_15, x_134, x_135, x_136, x_137);
return x_138;
}
}
}
}
}
}
else
{
lean_object* x_139; size_t x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_13, 1);
x_140 = lean_ctor_get_usize(x_13, 2);
lean_inc(x_139);
lean_dec(x_13);
x_141 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_142 = lean_string_dec_eq(x_139, x_141);
lean_dec(x_139);
if (x_142 == 0)
{
lean_object* x_143; 
lean_free_object(x_12);
lean_dec(x_25);
lean_free_object(x_11);
lean_dec(x_21);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_apply_1(x_9, x_1);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_144 = x_1;
} else {
 lean_dec_ref(x_1);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_146 = lean_string_dec_eq(x_25, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_147, 0, x_14);
lean_ctor_set(x_147, 1, x_141);
lean_ctor_set_usize(x_147, 2, x_140);
lean_ctor_set(x_12, 0, x_147);
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_144;
}
lean_ctor_set(x_148, 0, x_10);
lean_ctor_set(x_148, 1, x_15);
x_149 = lean_apply_1(x_9, x_148);
return x_149;
}
else
{
lean_object* x_150; uint8_t x_151; 
lean_dec(x_25);
x_150 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_151 = lean_string_dec_eq(x_21, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_152, 0, x_14);
lean_ctor_set(x_152, 1, x_141);
lean_ctor_set_usize(x_152, 2, x_140);
lean_ctor_set(x_12, 1, x_145);
lean_ctor_set(x_12, 0, x_152);
if (lean_is_scalar(x_144)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_144;
}
lean_ctor_set(x_153, 0, x_10);
lean_ctor_set(x_153, 1, x_15);
x_154 = lean_apply_1(x_9, x_153);
return x_154;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_21);
x_155 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_156 = lean_string_dec_eq(x_17, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_2);
x_157 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_158 = lean_string_dec_eq(x_17, x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_3);
x_159 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_160 = lean_string_dec_eq(x_17, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
lean_dec(x_4);
x_161 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_162 = lean_string_dec_eq(x_17, x_161);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
lean_dec(x_5);
x_163 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_164 = lean_string_dec_eq(x_17, x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_6);
x_165 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_166 = lean_string_dec_eq(x_17, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_7);
x_167 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_167, 0, x_14);
lean_ctor_set(x_167, 1, x_141);
lean_ctor_set_usize(x_167, 2, x_140);
lean_ctor_set(x_12, 1, x_145);
lean_ctor_set(x_12, 0, x_167);
lean_ctor_set(x_11, 1, x_150);
if (lean_is_scalar(x_144)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_144;
}
lean_ctor_set(x_168, 0, x_10);
lean_ctor_set(x_168, 1, x_15);
x_169 = lean_apply_1(x_9, x_168);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_144);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
x_170 = lean_box_usize(x_140);
x_171 = lean_box_usize(x_26);
x_172 = lean_box_usize(x_22);
x_173 = lean_box_usize(x_18);
x_174 = lean_apply_5(x_7, x_15, x_170, x_171, x_172, x_173);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_144);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
x_175 = lean_box_usize(x_140);
x_176 = lean_box_usize(x_26);
x_177 = lean_box_usize(x_22);
x_178 = lean_box_usize(x_18);
x_179 = lean_apply_5(x_6, x_15, x_175, x_176, x_177, x_178);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_144);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_180 = lean_box_usize(x_140);
x_181 = lean_box_usize(x_26);
x_182 = lean_box_usize(x_22);
x_183 = lean_box_usize(x_18);
x_184 = lean_apply_5(x_5, x_15, x_180, x_181, x_182, x_183);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_144);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_185 = lean_box_usize(x_140);
x_186 = lean_box_usize(x_26);
x_187 = lean_box_usize(x_22);
x_188 = lean_box_usize(x_18);
x_189 = lean_apply_5(x_4, x_15, x_185, x_186, x_187, x_188);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_144);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_190 = lean_box_usize(x_140);
x_191 = lean_box_usize(x_26);
x_192 = lean_box_usize(x_22);
x_193 = lean_box_usize(x_18);
x_194 = lean_apply_5(x_3, x_15, x_190, x_191, x_192, x_193);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_144);
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = lean_box_usize(x_140);
x_196 = lean_box_usize(x_26);
x_197 = lean_box_usize(x_22);
x_198 = lean_box_usize(x_18);
x_199 = lean_apply_5(x_2, x_15, x_195, x_196, x_197, x_198);
return x_199;
}
}
}
}
}
}
else
{
lean_object* x_200; size_t x_201; lean_object* x_202; size_t x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_200 = lean_ctor_get(x_12, 1);
x_201 = lean_ctor_get_usize(x_12, 2);
lean_inc(x_200);
lean_dec(x_12);
x_202 = lean_ctor_get(x_13, 1);
lean_inc(x_202);
x_203 = lean_ctor_get_usize(x_13, 2);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_204 = x_13;
} else {
 lean_dec_ref(x_13);
 x_204 = lean_box(0);
}
x_205 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_206 = lean_string_dec_eq(x_202, x_205);
lean_dec(x_202);
if (x_206 == 0)
{
lean_object* x_207; 
lean_dec(x_204);
lean_dec(x_200);
lean_free_object(x_11);
lean_dec(x_21);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_apply_1(x_9, x_1);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_208 = x_1;
} else {
 lean_dec_ref(x_1);
 x_208 = lean_box(0);
}
x_209 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_210 = lean_string_dec_eq(x_200, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_204)) {
 x_211 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_211 = x_204;
}
lean_ctor_set(x_211, 0, x_14);
lean_ctor_set(x_211, 1, x_205);
lean_ctor_set_usize(x_211, 2, x_203);
x_212 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_200);
lean_ctor_set_usize(x_212, 2, x_201);
lean_ctor_set(x_11, 0, x_212);
if (lean_is_scalar(x_208)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_208;
}
lean_ctor_set(x_213, 0, x_10);
lean_ctor_set(x_213, 1, x_15);
x_214 = lean_apply_1(x_9, x_213);
return x_214;
}
else
{
lean_object* x_215; uint8_t x_216; 
lean_dec(x_200);
x_215 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_216 = lean_string_dec_eq(x_21, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_204)) {
 x_217 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_217 = x_204;
}
lean_ctor_set(x_217, 0, x_14);
lean_ctor_set(x_217, 1, x_205);
lean_ctor_set_usize(x_217, 2, x_203);
x_218 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_209);
lean_ctor_set_usize(x_218, 2, x_201);
lean_ctor_set(x_11, 0, x_218);
if (lean_is_scalar(x_208)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_208;
}
lean_ctor_set(x_219, 0, x_10);
lean_ctor_set(x_219, 1, x_15);
x_220 = lean_apply_1(x_9, x_219);
return x_220;
}
else
{
lean_object* x_221; uint8_t x_222; 
lean_dec(x_21);
x_221 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_222 = lean_string_dec_eq(x_17, x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_2);
x_223 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_224 = lean_string_dec_eq(x_17, x_223);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; 
lean_dec(x_3);
x_225 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_226 = lean_string_dec_eq(x_17, x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
lean_dec(x_4);
x_227 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_228 = lean_string_dec_eq(x_17, x_227);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
lean_dec(x_5);
x_229 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_230 = lean_string_dec_eq(x_17, x_229);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
lean_dec(x_6);
x_231 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_232 = lean_string_dec_eq(x_17, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_7);
if (lean_is_scalar(x_204)) {
 x_233 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_233 = x_204;
}
lean_ctor_set(x_233, 0, x_14);
lean_ctor_set(x_233, 1, x_205);
lean_ctor_set_usize(x_233, 2, x_203);
x_234 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_209);
lean_ctor_set_usize(x_234, 2, x_201);
lean_ctor_set(x_11, 1, x_215);
lean_ctor_set(x_11, 0, x_234);
if (lean_is_scalar(x_208)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_208;
}
lean_ctor_set(x_235, 0, x_10);
lean_ctor_set(x_235, 1, x_15);
x_236 = lean_apply_1(x_9, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_208);
lean_dec(x_204);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
x_237 = lean_box_usize(x_203);
x_238 = lean_box_usize(x_201);
x_239 = lean_box_usize(x_22);
x_240 = lean_box_usize(x_18);
x_241 = lean_apply_5(x_7, x_15, x_237, x_238, x_239, x_240);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_208);
lean_dec(x_204);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
x_242 = lean_box_usize(x_203);
x_243 = lean_box_usize(x_201);
x_244 = lean_box_usize(x_22);
x_245 = lean_box_usize(x_18);
x_246 = lean_apply_5(x_6, x_15, x_242, x_243, x_244, x_245);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_208);
lean_dec(x_204);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_247 = lean_box_usize(x_203);
x_248 = lean_box_usize(x_201);
x_249 = lean_box_usize(x_22);
x_250 = lean_box_usize(x_18);
x_251 = lean_apply_5(x_5, x_15, x_247, x_248, x_249, x_250);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_208);
lean_dec(x_204);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_252 = lean_box_usize(x_203);
x_253 = lean_box_usize(x_201);
x_254 = lean_box_usize(x_22);
x_255 = lean_box_usize(x_18);
x_256 = lean_apply_5(x_4, x_15, x_252, x_253, x_254, x_255);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_208);
lean_dec(x_204);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_257 = lean_box_usize(x_203);
x_258 = lean_box_usize(x_201);
x_259 = lean_box_usize(x_22);
x_260 = lean_box_usize(x_18);
x_261 = lean_apply_5(x_3, x_15, x_257, x_258, x_259, x_260);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_208);
lean_dec(x_204);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_262 = lean_box_usize(x_203);
x_263 = lean_box_usize(x_201);
x_264 = lean_box_usize(x_22);
x_265 = lean_box_usize(x_18);
x_266 = lean_apply_5(x_2, x_15, x_262, x_263, x_264, x_265);
return x_266;
}
}
}
}
}
}
else
{
lean_object* x_267; size_t x_268; lean_object* x_269; size_t x_270; lean_object* x_271; lean_object* x_272; size_t x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_267 = lean_ctor_get(x_11, 1);
x_268 = lean_ctor_get_usize(x_11, 2);
lean_inc(x_267);
lean_dec(x_11);
x_269 = lean_ctor_get(x_12, 1);
lean_inc(x_269);
x_270 = lean_ctor_get_usize(x_12, 2);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_271 = x_12;
} else {
 lean_dec_ref(x_12);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_13, 1);
lean_inc(x_272);
x_273 = lean_ctor_get_usize(x_13, 2);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_274 = x_13;
} else {
 lean_dec_ref(x_13);
 x_274 = lean_box(0);
}
x_275 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_276 = lean_string_dec_eq(x_272, x_275);
lean_dec(x_272);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_274);
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_267);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = lean_apply_1(x_9, x_1);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_278 = x_1;
} else {
 lean_dec_ref(x_1);
 x_278 = lean_box(0);
}
x_279 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_280 = lean_string_dec_eq(x_269, x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_274)) {
 x_281 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_281 = x_274;
}
lean_ctor_set(x_281, 0, x_14);
lean_ctor_set(x_281, 1, x_275);
lean_ctor_set_usize(x_281, 2, x_273);
if (lean_is_scalar(x_271)) {
 x_282 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_282 = x_271;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_269);
lean_ctor_set_usize(x_282, 2, x_270);
x_283 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_267);
lean_ctor_set_usize(x_283, 2, x_268);
lean_ctor_set(x_10, 0, x_283);
if (lean_is_scalar(x_278)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_278;
}
lean_ctor_set(x_284, 0, x_10);
lean_ctor_set(x_284, 1, x_15);
x_285 = lean_apply_1(x_9, x_284);
return x_285;
}
else
{
lean_object* x_286; uint8_t x_287; 
lean_dec(x_269);
x_286 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_287 = lean_string_dec_eq(x_267, x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_274)) {
 x_288 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_288 = x_274;
}
lean_ctor_set(x_288, 0, x_14);
lean_ctor_set(x_288, 1, x_275);
lean_ctor_set_usize(x_288, 2, x_273);
if (lean_is_scalar(x_271)) {
 x_289 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_289 = x_271;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_279);
lean_ctor_set_usize(x_289, 2, x_270);
x_290 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_267);
lean_ctor_set_usize(x_290, 2, x_268);
lean_ctor_set(x_10, 0, x_290);
if (lean_is_scalar(x_278)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_278;
}
lean_ctor_set(x_291, 0, x_10);
lean_ctor_set(x_291, 1, x_15);
x_292 = lean_apply_1(x_9, x_291);
return x_292;
}
else
{
lean_object* x_293; uint8_t x_294; 
lean_dec(x_267);
x_293 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_294 = lean_string_dec_eq(x_17, x_293);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
lean_dec(x_2);
x_295 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_296 = lean_string_dec_eq(x_17, x_295);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_3);
x_297 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_298 = lean_string_dec_eq(x_17, x_297);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; 
lean_dec(x_4);
x_299 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_300 = lean_string_dec_eq(x_17, x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
lean_dec(x_5);
x_301 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_302 = lean_string_dec_eq(x_17, x_301);
if (x_302 == 0)
{
lean_object* x_303; uint8_t x_304; 
lean_dec(x_6);
x_303 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_304 = lean_string_dec_eq(x_17, x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_7);
if (lean_is_scalar(x_274)) {
 x_305 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_305 = x_274;
}
lean_ctor_set(x_305, 0, x_14);
lean_ctor_set(x_305, 1, x_275);
lean_ctor_set_usize(x_305, 2, x_273);
if (lean_is_scalar(x_271)) {
 x_306 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_306 = x_271;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_279);
lean_ctor_set_usize(x_306, 2, x_270);
x_307 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_286);
lean_ctor_set_usize(x_307, 2, x_268);
lean_ctor_set(x_10, 0, x_307);
if (lean_is_scalar(x_278)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_278;
}
lean_ctor_set(x_308, 0, x_10);
lean_ctor_set(x_308, 1, x_15);
x_309 = lean_apply_1(x_9, x_308);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_278);
lean_dec(x_274);
lean_dec(x_271);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
x_310 = lean_box_usize(x_273);
x_311 = lean_box_usize(x_270);
x_312 = lean_box_usize(x_268);
x_313 = lean_box_usize(x_18);
x_314 = lean_apply_5(x_7, x_15, x_310, x_311, x_312, x_313);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_278);
lean_dec(x_274);
lean_dec(x_271);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
x_315 = lean_box_usize(x_273);
x_316 = lean_box_usize(x_270);
x_317 = lean_box_usize(x_268);
x_318 = lean_box_usize(x_18);
x_319 = lean_apply_5(x_6, x_15, x_315, x_316, x_317, x_318);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_278);
lean_dec(x_274);
lean_dec(x_271);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_320 = lean_box_usize(x_273);
x_321 = lean_box_usize(x_270);
x_322 = lean_box_usize(x_268);
x_323 = lean_box_usize(x_18);
x_324 = lean_apply_5(x_5, x_15, x_320, x_321, x_322, x_323);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_278);
lean_dec(x_274);
lean_dec(x_271);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_325 = lean_box_usize(x_273);
x_326 = lean_box_usize(x_270);
x_327 = lean_box_usize(x_268);
x_328 = lean_box_usize(x_18);
x_329 = lean_apply_5(x_4, x_15, x_325, x_326, x_327, x_328);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_278);
lean_dec(x_274);
lean_dec(x_271);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_330 = lean_box_usize(x_273);
x_331 = lean_box_usize(x_270);
x_332 = lean_box_usize(x_268);
x_333 = lean_box_usize(x_18);
x_334 = lean_apply_5(x_3, x_15, x_330, x_331, x_332, x_333);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_278);
lean_dec(x_274);
lean_dec(x_271);
lean_free_object(x_10);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_335 = lean_box_usize(x_273);
x_336 = lean_box_usize(x_270);
x_337 = lean_box_usize(x_268);
x_338 = lean_box_usize(x_18);
x_339 = lean_apply_5(x_2, x_15, x_335, x_336, x_337, x_338);
return x_339;
}
}
}
}
}
}
else
{
lean_object* x_340; size_t x_341; lean_object* x_342; size_t x_343; lean_object* x_344; lean_object* x_345; size_t x_346; lean_object* x_347; lean_object* x_348; size_t x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_340 = lean_ctor_get(x_10, 1);
x_341 = lean_ctor_get_usize(x_10, 2);
lean_inc(x_340);
lean_dec(x_10);
x_342 = lean_ctor_get(x_11, 1);
lean_inc(x_342);
x_343 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_344 = x_11;
} else {
 lean_dec_ref(x_11);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_12, 1);
lean_inc(x_345);
x_346 = lean_ctor_get_usize(x_12, 2);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_347 = x_12;
} else {
 lean_dec_ref(x_12);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_13, 1);
lean_inc(x_348);
x_349 = lean_ctor_get_usize(x_13, 2);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_350 = x_13;
} else {
 lean_dec_ref(x_13);
 x_350 = lean_box(0);
}
x_351 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_352 = lean_string_dec_eq(x_348, x_351);
lean_dec(x_348);
if (x_352 == 0)
{
lean_object* x_353; 
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_353 = lean_apply_1(x_9, x_1);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_354 = x_1;
} else {
 lean_dec_ref(x_1);
 x_354 = lean_box(0);
}
x_355 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_356 = lean_string_dec_eq(x_345, x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_14);
lean_ctor_set(x_357, 1, x_351);
lean_ctor_set_usize(x_357, 2, x_349);
if (lean_is_scalar(x_347)) {
 x_358 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_358 = x_347;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_345);
lean_ctor_set_usize(x_358, 2, x_346);
if (lean_is_scalar(x_344)) {
 x_359 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_359 = x_344;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_342);
lean_ctor_set_usize(x_359, 2, x_343);
x_360 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_340);
lean_ctor_set_usize(x_360, 2, x_341);
if (lean_is_scalar(x_354)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_354;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_15);
x_362 = lean_apply_1(x_9, x_361);
return x_362;
}
else
{
lean_object* x_363; uint8_t x_364; 
lean_dec(x_345);
x_363 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_364 = lean_string_dec_eq(x_342, x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_350)) {
 x_365 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_365 = x_350;
}
lean_ctor_set(x_365, 0, x_14);
lean_ctor_set(x_365, 1, x_351);
lean_ctor_set_usize(x_365, 2, x_349);
if (lean_is_scalar(x_347)) {
 x_366 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_366 = x_347;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set_usize(x_366, 2, x_346);
if (lean_is_scalar(x_344)) {
 x_367 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_367 = x_344;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_342);
lean_ctor_set_usize(x_367, 2, x_343);
x_368 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_340);
lean_ctor_set_usize(x_368, 2, x_341);
if (lean_is_scalar(x_354)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_354;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_15);
x_370 = lean_apply_1(x_9, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; 
lean_dec(x_342);
x_371 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_372 = lean_string_dec_eq(x_340, x_371);
if (x_372 == 0)
{
lean_object* x_373; uint8_t x_374; 
lean_dec(x_2);
x_373 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_374 = lean_string_dec_eq(x_340, x_373);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
lean_dec(x_3);
x_375 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_376 = lean_string_dec_eq(x_340, x_375);
if (x_376 == 0)
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_4);
x_377 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_378 = lean_string_dec_eq(x_340, x_377);
if (x_378 == 0)
{
lean_object* x_379; uint8_t x_380; 
lean_dec(x_5);
x_379 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_380 = lean_string_dec_eq(x_340, x_379);
if (x_380 == 0)
{
lean_object* x_381; uint8_t x_382; 
lean_dec(x_6);
x_381 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_382 = lean_string_dec_eq(x_340, x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_7);
if (lean_is_scalar(x_350)) {
 x_383 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_383 = x_350;
}
lean_ctor_set(x_383, 0, x_14);
lean_ctor_set(x_383, 1, x_351);
lean_ctor_set_usize(x_383, 2, x_349);
if (lean_is_scalar(x_347)) {
 x_384 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_384 = x_347;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_355);
lean_ctor_set_usize(x_384, 2, x_346);
if (lean_is_scalar(x_344)) {
 x_385 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_385 = x_344;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_363);
lean_ctor_set_usize(x_385, 2, x_343);
x_386 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_340);
lean_ctor_set_usize(x_386, 2, x_341);
if (lean_is_scalar(x_354)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_354;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_15);
x_388 = lean_apply_1(x_9, x_387);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_9);
x_389 = lean_box_usize(x_349);
x_390 = lean_box_usize(x_346);
x_391 = lean_box_usize(x_343);
x_392 = lean_box_usize(x_341);
x_393 = lean_apply_5(x_7, x_15, x_389, x_390, x_391, x_392);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_7);
x_394 = lean_box_usize(x_349);
x_395 = lean_box_usize(x_346);
x_396 = lean_box_usize(x_343);
x_397 = lean_box_usize(x_341);
x_398 = lean_apply_5(x_6, x_15, x_394, x_395, x_396, x_397);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_399 = lean_box_usize(x_349);
x_400 = lean_box_usize(x_346);
x_401 = lean_box_usize(x_343);
x_402 = lean_box_usize(x_341);
x_403 = lean_apply_5(x_5, x_15, x_399, x_400, x_401, x_402);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_404 = lean_box_usize(x_349);
x_405 = lean_box_usize(x_346);
x_406 = lean_box_usize(x_343);
x_407 = lean_box_usize(x_341);
x_408 = lean_apply_5(x_4, x_15, x_404, x_405, x_406, x_407);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_409 = lean_box_usize(x_349);
x_410 = lean_box_usize(x_346);
x_411 = lean_box_usize(x_343);
x_412 = lean_box_usize(x_341);
x_413 = lean_apply_5(x_3, x_15, x_409, x_410, x_411, x_412);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_414 = lean_box_usize(x_349);
x_415 = lean_box_usize(x_346);
x_416 = lean_box_usize(x_343);
x_417 = lean_box_usize(x_341);
x_418 = lean_apply_5(x_2, x_15, x_414, x_415, x_416, x_417);
return x_418;
}
}
}
}
}
}
else
{
lean_object* x_419; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_419 = lean_apply_1(x_9, x_1);
return x_419;
}
}
else
{
lean_object* x_420; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_420 = lean_apply_1(x_9, x_1);
return x_420;
}
}
else
{
lean_object* x_421; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_421 = lean_apply_1(x_9, x_1);
return x_421;
}
}
else
{
lean_object* x_422; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_422 = lean_apply_1(x_9, x_1);
return x_422;
}
}
else
{
lean_object* x_423; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_423 = lean_apply_1(x_9, x_1);
return x_423;
}
}
case 3:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_424 = lean_ctor_get(x_1, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_1, 2);
lean_inc(x_426);
x_427 = lean_ctor_get(x_1, 3);
lean_inc(x_427);
lean_dec(x_1);
x_428 = lean_apply_4(x_8, x_424, x_425, x_426, x_427);
return x_428;
}
default: 
{
lean_object* x_429; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_429 = lean_apply_1(x_9, x_1);
return x_429;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders_loop_match__3___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lean_Elab_Term_expandFunBinders_loop___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_mkArrow___closed__2;
x_9 = l_Lean_addMacroScope(x_7, x_8, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Meta_mkArrow___closed__2;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at_Lean_Elab_Term_expandFunBinders_loop___spec__2(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_mkIdentFrom(x_1, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_mkIdentFrom(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_mkExplicitBinder(x_10, x_1);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fget(x_1, x_3);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_20 = l_Lean_mkHole(x_14);
lean_inc(x_16);
x_21 = l_Lean_Elab_Term_mkExplicitBinder(x_16, x_20);
x_22 = lean_array_push(x_4, x_21);
lean_inc(x_5);
x_23 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_19, x_22, x_5, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_dec(x_31);
x_32 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_26);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_34);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_empty___closed__1;
x_38 = lean_array_push(x_37, x_36);
x_39 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_40 = lean_array_push(x_38, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_42 = lean_array_push(x_41, x_16);
x_43 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_push(x_37, x_44);
x_46 = l_Lean_nullKind___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_push(x_40, x_47);
x_49 = lean_array_push(x_48, x_39);
x_50 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_34);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_49, x_51);
x_53 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_34);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_34);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_37, x_54);
x_56 = lean_array_push(x_37, x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_55, x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_34);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_push(x_58, x_60);
x_62 = lean_array_push(x_61, x_30);
x_63 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_37, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_46);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_37, x_66);
x_68 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_array_push(x_52, x_69);
x_71 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = 1;
x_74 = lean_box(x_73);
lean_ctor_set(x_25, 1, x_74);
lean_ctor_set(x_25, 0, x_72);
lean_ctor_set(x_32, 0, x_24);
return x_32;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_75 = lean_ctor_get(x_32, 0);
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_32);
x_77 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_75);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Array_empty___closed__1;
x_80 = lean_array_push(x_79, x_78);
x_81 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_82 = lean_array_push(x_80, x_81);
x_83 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_84 = lean_array_push(x_83, x_16);
x_85 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_79, x_86);
x_88 = l_Lean_nullKind___closed__2;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_array_push(x_82, x_89);
x_91 = lean_array_push(x_90, x_81);
x_92 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_75);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_array_push(x_91, x_93);
x_95 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_75);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_75);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_79, x_96);
x_98 = lean_array_push(x_79, x_14);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_push(x_97, x_99);
x_101 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_75);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_array_push(x_100, x_102);
x_104 = lean_array_push(x_103, x_30);
x_105 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_array_push(x_79, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_88);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_array_push(x_79, x_108);
x_110 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_array_push(x_94, x_111);
x_113 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = 1;
x_116 = lean_box(x_115);
lean_ctor_set(x_25, 1, x_116);
lean_ctor_set(x_25, 0, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_24);
lean_ctor_set(x_117, 1, x_76);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_118 = lean_ctor_get(x_25, 0);
lean_inc(x_118);
lean_dec(x_25);
x_119 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_26);
lean_dec(x_5);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_120);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_empty___closed__1;
x_126 = lean_array_push(x_125, x_124);
x_127 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_128 = lean_array_push(x_126, x_127);
x_129 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_130 = lean_array_push(x_129, x_16);
x_131 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_push(x_125, x_132);
x_134 = l_Lean_nullKind___closed__2;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_128, x_135);
x_137 = lean_array_push(x_136, x_127);
x_138 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_120);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_120);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_137, x_139);
x_141 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_120);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_120);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_push(x_125, x_142);
x_144 = lean_array_push(x_125, x_14);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_134);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_array_push(x_143, x_145);
x_147 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_120);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_push(x_146, x_148);
x_150 = lean_array_push(x_149, x_118);
x_151 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_125, x_152);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_134);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_array_push(x_125, x_154);
x_156 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_array_push(x_140, x_157);
x_159 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = 1;
x_162 = lean_box(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_24, 1, x_163);
if (lean_is_scalar(x_122)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_122;
}
lean_ctor_set(x_164, 0, x_24);
lean_ctor_set(x_164, 1, x_121);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_165 = lean_ctor_get(x_24, 0);
lean_inc(x_165);
lean_dec(x_24);
x_166 = lean_ctor_get(x_25, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_167 = x_25;
} else {
 lean_dec_ref(x_25);
 x_167 = lean_box(0);
}
x_168 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_26);
lean_dec(x_5);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_169);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Array_empty___closed__1;
x_175 = lean_array_push(x_174, x_173);
x_176 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_177 = lean_array_push(x_175, x_176);
x_178 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_179 = lean_array_push(x_178, x_16);
x_180 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_array_push(x_174, x_181);
x_183 = l_Lean_nullKind___closed__2;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_array_push(x_177, x_184);
x_186 = lean_array_push(x_185, x_176);
x_187 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_169);
x_188 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_188, 0, x_169);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_array_push(x_186, x_188);
x_190 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_169);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_169);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_array_push(x_174, x_191);
x_193 = lean_array_push(x_174, x_14);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_183);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_array_push(x_192, x_194);
x_196 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_169);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_array_push(x_195, x_197);
x_199 = lean_array_push(x_198, x_166);
x_200 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = lean_array_push(x_174, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_183);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_array_push(x_174, x_203);
x_205 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = lean_array_push(x_189, x_206);
x_208 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = 1;
x_211 = lean_box(x_210);
if (lean_is_scalar(x_167)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_167;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_165);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_171)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_171;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_170);
return x_214;
}
}
case 1:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_14, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 1)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
if (lean_obj_tag(x_216) == 1)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 1)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 1)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
lean_dec(x_215);
x_221 = lean_ctor_get(x_216, 1);
lean_inc(x_221);
lean_dec(x_216);
x_222 = lean_ctor_get(x_217, 1);
lean_inc(x_222);
lean_dec(x_217);
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
lean_dec(x_218);
x_224 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_225 = lean_string_dec_eq(x_223, x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_inc(x_5);
x_226 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_unsigned_to_nat(1u);
x_230 = lean_nat_add(x_3, x_229);
lean_dec(x_3);
x_231 = l_Lean_mkHole(x_14);
lean_inc(x_227);
x_232 = l_Lean_Elab_Term_mkExplicitBinder(x_227, x_231);
x_233 = lean_array_push(x_4, x_232);
lean_inc(x_5);
x_234 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_230, x_233, x_5, x_228);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = !lean_is_exclusive(x_235);
if (x_238 == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_235, 1);
lean_dec(x_239);
x_240 = !lean_is_exclusive(x_236);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_241 = lean_ctor_get(x_236, 0);
x_242 = lean_ctor_get(x_236, 1);
lean_dec(x_242);
x_243 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_237);
lean_dec(x_5);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_245);
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Array_empty___closed__1;
x_249 = lean_array_push(x_248, x_247);
x_250 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_251 = lean_array_push(x_249, x_250);
x_252 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_253 = lean_array_push(x_252, x_227);
x_254 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = lean_array_push(x_248, x_255);
x_257 = l_Lean_nullKind___closed__2;
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
x_259 = lean_array_push(x_251, x_258);
x_260 = lean_array_push(x_259, x_250);
x_261 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_245);
x_262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_262, 0, x_245);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_array_push(x_260, x_262);
x_264 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_245);
x_265 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_265, 0, x_245);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_array_push(x_248, x_265);
lean_inc(x_14);
x_267 = lean_array_push(x_248, x_14);
x_268 = !lean_is_exclusive(x_14);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; 
x_269 = lean_ctor_get(x_14, 1);
lean_dec(x_269);
x_270 = lean_ctor_get(x_14, 0);
lean_dec(x_270);
lean_ctor_set(x_14, 1, x_267);
lean_ctor_set(x_14, 0, x_257);
x_271 = lean_array_push(x_266, x_14);
x_272 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_273 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_273, 0, x_245);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_array_push(x_271, x_273);
x_275 = lean_array_push(x_274, x_241);
x_276 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = lean_array_push(x_248, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_257);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_array_push(x_248, x_279);
x_281 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = lean_array_push(x_263, x_282);
x_284 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
x_286 = 1;
x_287 = lean_box(x_286);
lean_ctor_set(x_236, 1, x_287);
lean_ctor_set(x_236, 0, x_285);
lean_ctor_set(x_243, 0, x_235);
return x_243;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; 
lean_dec(x_14);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_257);
lean_ctor_set(x_288, 1, x_267);
x_289 = lean_array_push(x_266, x_288);
x_290 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_291 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_291, 0, x_245);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_array_push(x_289, x_291);
x_293 = lean_array_push(x_292, x_241);
x_294 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_293);
x_296 = lean_array_push(x_248, x_295);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_257);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_array_push(x_248, x_297);
x_299 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
x_301 = lean_array_push(x_263, x_300);
x_302 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
x_304 = 1;
x_305 = lean_box(x_304);
lean_ctor_set(x_236, 1, x_305);
lean_ctor_set(x_236, 0, x_303);
lean_ctor_set(x_243, 0, x_235);
return x_243;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; 
x_306 = lean_ctor_get(x_243, 0);
x_307 = lean_ctor_get(x_243, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_243);
x_308 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_306);
x_309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_308);
x_310 = l_Array_empty___closed__1;
x_311 = lean_array_push(x_310, x_309);
x_312 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_313 = lean_array_push(x_311, x_312);
x_314 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_315 = lean_array_push(x_314, x_227);
x_316 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
x_318 = lean_array_push(x_310, x_317);
x_319 = l_Lean_nullKind___closed__2;
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = lean_array_push(x_313, x_320);
x_322 = lean_array_push(x_321, x_312);
x_323 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_306);
x_324 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_324, 0, x_306);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_array_push(x_322, x_324);
x_326 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_306);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_306);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_array_push(x_310, x_327);
lean_inc(x_14);
x_329 = lean_array_push(x_310, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_330 = x_14;
} else {
 lean_dec_ref(x_14);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_319);
lean_ctor_set(x_331, 1, x_329);
x_332 = lean_array_push(x_328, x_331);
x_333 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_334, 0, x_306);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_array_push(x_332, x_334);
x_336 = lean_array_push(x_335, x_241);
x_337 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_array_push(x_310, x_338);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_319);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_array_push(x_310, x_340);
x_342 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
x_344 = lean_array_push(x_325, x_343);
x_345 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
x_347 = 1;
x_348 = lean_box(x_347);
lean_ctor_set(x_236, 1, x_348);
lean_ctor_set(x_236, 0, x_346);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_235);
lean_ctor_set(x_349, 1, x_307);
return x_349;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_350 = lean_ctor_get(x_236, 0);
lean_inc(x_350);
lean_dec(x_236);
x_351 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_237);
lean_dec(x_5);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_352);
x_356 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_356, 0, x_352);
lean_ctor_set(x_356, 1, x_355);
x_357 = l_Array_empty___closed__1;
x_358 = lean_array_push(x_357, x_356);
x_359 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_360 = lean_array_push(x_358, x_359);
x_361 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_362 = lean_array_push(x_361, x_227);
x_363 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = lean_array_push(x_357, x_364);
x_366 = l_Lean_nullKind___closed__2;
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = lean_array_push(x_360, x_367);
x_369 = lean_array_push(x_368, x_359);
x_370 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_352);
x_371 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_371, 0, x_352);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_array_push(x_369, x_371);
x_373 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_352);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_352);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_array_push(x_357, x_374);
lean_inc(x_14);
x_376 = lean_array_push(x_357, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_377 = x_14;
} else {
 lean_dec_ref(x_14);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_366);
lean_ctor_set(x_378, 1, x_376);
x_379 = lean_array_push(x_375, x_378);
x_380 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_381 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_381, 0, x_352);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_array_push(x_379, x_381);
x_383 = lean_array_push(x_382, x_350);
x_384 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = lean_array_push(x_357, x_385);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_366);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_array_push(x_357, x_387);
x_389 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_388);
x_391 = lean_array_push(x_372, x_390);
x_392 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_391);
x_394 = 1;
x_395 = lean_box(x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_395);
lean_ctor_set(x_235, 1, x_396);
if (lean_is_scalar(x_354)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_354;
}
lean_ctor_set(x_397, 0, x_235);
lean_ctor_set(x_397, 1, x_353);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_398 = lean_ctor_get(x_235, 0);
lean_inc(x_398);
lean_dec(x_235);
x_399 = lean_ctor_get(x_236, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_400 = x_236;
} else {
 lean_dec_ref(x_236);
 x_400 = lean_box(0);
}
x_401 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_237);
lean_dec(x_5);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_405 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_402);
x_406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Array_empty___closed__1;
x_408 = lean_array_push(x_407, x_406);
x_409 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_410 = lean_array_push(x_408, x_409);
x_411 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_412 = lean_array_push(x_411, x_227);
x_413 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_412);
x_415 = lean_array_push(x_407, x_414);
x_416 = l_Lean_nullKind___closed__2;
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
x_418 = lean_array_push(x_410, x_417);
x_419 = lean_array_push(x_418, x_409);
x_420 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_402);
x_421 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_421, 0, x_402);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_array_push(x_419, x_421);
x_423 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_402);
x_424 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_424, 0, x_402);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_array_push(x_407, x_424);
lean_inc(x_14);
x_426 = lean_array_push(x_407, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_427 = x_14;
} else {
 lean_dec_ref(x_14);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_416);
lean_ctor_set(x_428, 1, x_426);
x_429 = lean_array_push(x_425, x_428);
x_430 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_431 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_431, 0, x_402);
lean_ctor_set(x_431, 1, x_430);
x_432 = lean_array_push(x_429, x_431);
x_433 = lean_array_push(x_432, x_399);
x_434 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_433);
x_436 = lean_array_push(x_407, x_435);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_416);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_array_push(x_407, x_437);
x_439 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_array_push(x_422, x_440);
x_442 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
x_444 = 1;
x_445 = lean_box(x_444);
if (lean_is_scalar(x_400)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_400;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_398);
lean_ctor_set(x_447, 1, x_446);
if (lean_is_scalar(x_404)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_404;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_403);
return x_448;
}
}
else
{
lean_object* x_449; uint8_t x_450; 
x_449 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_450 = lean_string_dec_eq(x_222, x_449);
lean_dec(x_222);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_221);
lean_dec(x_220);
lean_inc(x_5);
x_451 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_unsigned_to_nat(1u);
x_455 = lean_nat_add(x_3, x_454);
lean_dec(x_3);
x_456 = l_Lean_mkHole(x_14);
lean_inc(x_452);
x_457 = l_Lean_Elab_Term_mkExplicitBinder(x_452, x_456);
x_458 = lean_array_push(x_4, x_457);
lean_inc(x_5);
x_459 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_455, x_458, x_5, x_453);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
lean_dec(x_459);
x_463 = !lean_is_exclusive(x_460);
if (x_463 == 0)
{
lean_object* x_464; uint8_t x_465; 
x_464 = lean_ctor_get(x_460, 1);
lean_dec(x_464);
x_465 = !lean_is_exclusive(x_461);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_466 = lean_ctor_get(x_461, 0);
x_467 = lean_ctor_get(x_461, 1);
lean_dec(x_467);
x_468 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_462);
lean_dec(x_5);
x_469 = !lean_is_exclusive(x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_470 = lean_ctor_get(x_468, 0);
x_471 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_470);
x_472 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Array_empty___closed__1;
x_474 = lean_array_push(x_473, x_472);
x_475 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_476 = lean_array_push(x_474, x_475);
x_477 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_478 = lean_array_push(x_477, x_452);
x_479 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_478);
x_481 = lean_array_push(x_473, x_480);
x_482 = l_Lean_nullKind___closed__2;
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_481);
x_484 = lean_array_push(x_476, x_483);
x_485 = lean_array_push(x_484, x_475);
x_486 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_470);
x_487 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_487, 0, x_470);
lean_ctor_set(x_487, 1, x_486);
x_488 = lean_array_push(x_485, x_487);
x_489 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_470);
x_490 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_490, 0, x_470);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_array_push(x_473, x_490);
lean_inc(x_14);
x_492 = lean_array_push(x_473, x_14);
x_493 = !lean_is_exclusive(x_14);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_494 = lean_ctor_get(x_14, 1);
lean_dec(x_494);
x_495 = lean_ctor_get(x_14, 0);
lean_dec(x_495);
lean_ctor_set(x_14, 1, x_492);
lean_ctor_set(x_14, 0, x_482);
x_496 = lean_array_push(x_491, x_14);
x_497 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_498 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_498, 0, x_470);
lean_ctor_set(x_498, 1, x_497);
x_499 = lean_array_push(x_496, x_498);
x_500 = lean_array_push(x_499, x_466);
x_501 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_500);
x_503 = lean_array_push(x_473, x_502);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_482);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_array_push(x_473, x_504);
x_506 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_505);
x_508 = lean_array_push(x_488, x_507);
x_509 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
x_511 = 1;
x_512 = lean_box(x_511);
lean_ctor_set(x_461, 1, x_512);
lean_ctor_set(x_461, 0, x_510);
lean_ctor_set(x_468, 0, x_460);
return x_468;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; 
lean_dec(x_14);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_482);
lean_ctor_set(x_513, 1, x_492);
x_514 = lean_array_push(x_491, x_513);
x_515 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_516 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_516, 0, x_470);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_array_push(x_514, x_516);
x_518 = lean_array_push(x_517, x_466);
x_519 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_518);
x_521 = lean_array_push(x_473, x_520);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_482);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_array_push(x_473, x_522);
x_524 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_523);
x_526 = lean_array_push(x_488, x_525);
x_527 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_526);
x_529 = 1;
x_530 = lean_box(x_529);
lean_ctor_set(x_461, 1, x_530);
lean_ctor_set(x_461, 0, x_528);
lean_ctor_set(x_468, 0, x_460);
return x_468;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; 
x_531 = lean_ctor_get(x_468, 0);
x_532 = lean_ctor_get(x_468, 1);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_468);
x_533 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_531);
x_534 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_534, 0, x_531);
lean_ctor_set(x_534, 1, x_533);
x_535 = l_Array_empty___closed__1;
x_536 = lean_array_push(x_535, x_534);
x_537 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_538 = lean_array_push(x_536, x_537);
x_539 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_540 = lean_array_push(x_539, x_452);
x_541 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
x_543 = lean_array_push(x_535, x_542);
x_544 = l_Lean_nullKind___closed__2;
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = lean_array_push(x_538, x_545);
x_547 = lean_array_push(x_546, x_537);
x_548 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_531);
x_549 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_549, 0, x_531);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_array_push(x_547, x_549);
x_551 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_531);
x_552 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_552, 0, x_531);
lean_ctor_set(x_552, 1, x_551);
x_553 = lean_array_push(x_535, x_552);
lean_inc(x_14);
x_554 = lean_array_push(x_535, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_555 = x_14;
} else {
 lean_dec_ref(x_14);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_544);
lean_ctor_set(x_556, 1, x_554);
x_557 = lean_array_push(x_553, x_556);
x_558 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_559, 0, x_531);
lean_ctor_set(x_559, 1, x_558);
x_560 = lean_array_push(x_557, x_559);
x_561 = lean_array_push(x_560, x_466);
x_562 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
x_564 = lean_array_push(x_535, x_563);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_544);
lean_ctor_set(x_565, 1, x_564);
x_566 = lean_array_push(x_535, x_565);
x_567 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_566);
x_569 = lean_array_push(x_550, x_568);
x_570 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
x_572 = 1;
x_573 = lean_box(x_572);
lean_ctor_set(x_461, 1, x_573);
lean_ctor_set(x_461, 0, x_571);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_460);
lean_ctor_set(x_574, 1, x_532);
return x_574;
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_575 = lean_ctor_get(x_461, 0);
lean_inc(x_575);
lean_dec(x_461);
x_576 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_462);
lean_dec(x_5);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_579 = x_576;
} else {
 lean_dec_ref(x_576);
 x_579 = lean_box(0);
}
x_580 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_577);
x_581 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_581, 0, x_577);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_Array_empty___closed__1;
x_583 = lean_array_push(x_582, x_581);
x_584 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_585 = lean_array_push(x_583, x_584);
x_586 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_587 = lean_array_push(x_586, x_452);
x_588 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_587);
x_590 = lean_array_push(x_582, x_589);
x_591 = l_Lean_nullKind___closed__2;
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_590);
x_593 = lean_array_push(x_585, x_592);
x_594 = lean_array_push(x_593, x_584);
x_595 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_577);
x_596 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_596, 0, x_577);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_array_push(x_594, x_596);
x_598 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_577);
x_599 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_599, 0, x_577);
lean_ctor_set(x_599, 1, x_598);
x_600 = lean_array_push(x_582, x_599);
lean_inc(x_14);
x_601 = lean_array_push(x_582, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_602 = x_14;
} else {
 lean_dec_ref(x_14);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_591);
lean_ctor_set(x_603, 1, x_601);
x_604 = lean_array_push(x_600, x_603);
x_605 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_606 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_606, 0, x_577);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_array_push(x_604, x_606);
x_608 = lean_array_push(x_607, x_575);
x_609 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_608);
x_611 = lean_array_push(x_582, x_610);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_591);
lean_ctor_set(x_612, 1, x_611);
x_613 = lean_array_push(x_582, x_612);
x_614 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_613);
x_616 = lean_array_push(x_597, x_615);
x_617 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_616);
x_619 = 1;
x_620 = lean_box(x_619);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_620);
lean_ctor_set(x_460, 1, x_621);
if (lean_is_scalar(x_579)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_579;
}
lean_ctor_set(x_622, 0, x_460);
lean_ctor_set(x_622, 1, x_578);
return x_622;
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_623 = lean_ctor_get(x_460, 0);
lean_inc(x_623);
lean_dec(x_460);
x_624 = lean_ctor_get(x_461, 0);
lean_inc(x_624);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_625 = x_461;
} else {
 lean_dec_ref(x_461);
 x_625 = lean_box(0);
}
x_626 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_462);
lean_dec(x_5);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 lean_ctor_release(x_626, 1);
 x_629 = x_626;
} else {
 lean_dec_ref(x_626);
 x_629 = lean_box(0);
}
x_630 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_627);
x_631 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_631, 0, x_627);
lean_ctor_set(x_631, 1, x_630);
x_632 = l_Array_empty___closed__1;
x_633 = lean_array_push(x_632, x_631);
x_634 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_635 = lean_array_push(x_633, x_634);
x_636 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_637 = lean_array_push(x_636, x_452);
x_638 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_637);
x_640 = lean_array_push(x_632, x_639);
x_641 = l_Lean_nullKind___closed__2;
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_640);
x_643 = lean_array_push(x_635, x_642);
x_644 = lean_array_push(x_643, x_634);
x_645 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_627);
x_646 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_646, 0, x_627);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_array_push(x_644, x_646);
x_648 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_627);
x_649 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_649, 0, x_627);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_array_push(x_632, x_649);
lean_inc(x_14);
x_651 = lean_array_push(x_632, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_652 = x_14;
} else {
 lean_dec_ref(x_14);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_641);
lean_ctor_set(x_653, 1, x_651);
x_654 = lean_array_push(x_650, x_653);
x_655 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_656 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_656, 0, x_627);
lean_ctor_set(x_656, 1, x_655);
x_657 = lean_array_push(x_654, x_656);
x_658 = lean_array_push(x_657, x_624);
x_659 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_658);
x_661 = lean_array_push(x_632, x_660);
x_662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_662, 0, x_641);
lean_ctor_set(x_662, 1, x_661);
x_663 = lean_array_push(x_632, x_662);
x_664 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_663);
x_666 = lean_array_push(x_647, x_665);
x_667 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_666);
x_669 = 1;
x_670 = lean_box(x_669);
if (lean_is_scalar(x_625)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_625;
}
lean_ctor_set(x_671, 0, x_668);
lean_ctor_set(x_671, 1, x_670);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_623);
lean_ctor_set(x_672, 1, x_671);
if (lean_is_scalar(x_629)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_629;
}
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_628);
return x_673;
}
}
else
{
lean_object* x_674; uint8_t x_675; 
x_674 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_675 = lean_string_dec_eq(x_221, x_674);
lean_dec(x_221);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; 
lean_dec(x_220);
lean_inc(x_5);
x_676 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_679 = lean_unsigned_to_nat(1u);
x_680 = lean_nat_add(x_3, x_679);
lean_dec(x_3);
x_681 = l_Lean_mkHole(x_14);
lean_inc(x_677);
x_682 = l_Lean_Elab_Term_mkExplicitBinder(x_677, x_681);
x_683 = lean_array_push(x_4, x_682);
lean_inc(x_5);
x_684 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_680, x_683, x_5, x_678);
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
x_687 = lean_ctor_get(x_684, 1);
lean_inc(x_687);
lean_dec(x_684);
x_688 = !lean_is_exclusive(x_685);
if (x_688 == 0)
{
lean_object* x_689; uint8_t x_690; 
x_689 = lean_ctor_get(x_685, 1);
lean_dec(x_689);
x_690 = !lean_is_exclusive(x_686);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
x_691 = lean_ctor_get(x_686, 0);
x_692 = lean_ctor_get(x_686, 1);
lean_dec(x_692);
x_693 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_687);
lean_dec(x_5);
x_694 = !lean_is_exclusive(x_693);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_718; 
x_695 = lean_ctor_get(x_693, 0);
x_696 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_695);
x_697 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
x_698 = l_Array_empty___closed__1;
x_699 = lean_array_push(x_698, x_697);
x_700 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_701 = lean_array_push(x_699, x_700);
x_702 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_703 = lean_array_push(x_702, x_677);
x_704 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
x_706 = lean_array_push(x_698, x_705);
x_707 = l_Lean_nullKind___closed__2;
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_706);
x_709 = lean_array_push(x_701, x_708);
x_710 = lean_array_push(x_709, x_700);
x_711 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_695);
x_712 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_712, 0, x_695);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_array_push(x_710, x_712);
x_714 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_695);
x_715 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_715, 0, x_695);
lean_ctor_set(x_715, 1, x_714);
x_716 = lean_array_push(x_698, x_715);
lean_inc(x_14);
x_717 = lean_array_push(x_698, x_14);
x_718 = !lean_is_exclusive(x_14);
if (x_718 == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; lean_object* x_737; 
x_719 = lean_ctor_get(x_14, 1);
lean_dec(x_719);
x_720 = lean_ctor_get(x_14, 0);
lean_dec(x_720);
lean_ctor_set(x_14, 1, x_717);
lean_ctor_set(x_14, 0, x_707);
x_721 = lean_array_push(x_716, x_14);
x_722 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_723 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_723, 0, x_695);
lean_ctor_set(x_723, 1, x_722);
x_724 = lean_array_push(x_721, x_723);
x_725 = lean_array_push(x_724, x_691);
x_726 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_725);
x_728 = lean_array_push(x_698, x_727);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_707);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_array_push(x_698, x_729);
x_731 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_730);
x_733 = lean_array_push(x_713, x_732);
x_734 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_735 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_733);
x_736 = 1;
x_737 = lean_box(x_736);
lean_ctor_set(x_686, 1, x_737);
lean_ctor_set(x_686, 0, x_735);
lean_ctor_set(x_693, 0, x_685);
return x_693;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; lean_object* x_755; 
lean_dec(x_14);
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_707);
lean_ctor_set(x_738, 1, x_717);
x_739 = lean_array_push(x_716, x_738);
x_740 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_741 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_741, 0, x_695);
lean_ctor_set(x_741, 1, x_740);
x_742 = lean_array_push(x_739, x_741);
x_743 = lean_array_push(x_742, x_691);
x_744 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_743);
x_746 = lean_array_push(x_698, x_745);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_707);
lean_ctor_set(x_747, 1, x_746);
x_748 = lean_array_push(x_698, x_747);
x_749 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_748);
x_751 = lean_array_push(x_713, x_750);
x_752 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_751);
x_754 = 1;
x_755 = lean_box(x_754);
lean_ctor_set(x_686, 1, x_755);
lean_ctor_set(x_686, 0, x_753);
lean_ctor_set(x_693, 0, x_685);
return x_693;
}
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; uint8_t x_797; lean_object* x_798; lean_object* x_799; 
x_756 = lean_ctor_get(x_693, 0);
x_757 = lean_ctor_get(x_693, 1);
lean_inc(x_757);
lean_inc(x_756);
lean_dec(x_693);
x_758 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_756);
x_759 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_759, 0, x_756);
lean_ctor_set(x_759, 1, x_758);
x_760 = l_Array_empty___closed__1;
x_761 = lean_array_push(x_760, x_759);
x_762 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_763 = lean_array_push(x_761, x_762);
x_764 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_765 = lean_array_push(x_764, x_677);
x_766 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_765);
x_768 = lean_array_push(x_760, x_767);
x_769 = l_Lean_nullKind___closed__2;
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_768);
x_771 = lean_array_push(x_763, x_770);
x_772 = lean_array_push(x_771, x_762);
x_773 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_756);
x_774 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_774, 0, x_756);
lean_ctor_set(x_774, 1, x_773);
x_775 = lean_array_push(x_772, x_774);
x_776 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_756);
x_777 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_777, 0, x_756);
lean_ctor_set(x_777, 1, x_776);
x_778 = lean_array_push(x_760, x_777);
lean_inc(x_14);
x_779 = lean_array_push(x_760, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_780 = x_14;
} else {
 lean_dec_ref(x_14);
 x_780 = lean_box(0);
}
if (lean_is_scalar(x_780)) {
 x_781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_781 = x_780;
}
lean_ctor_set(x_781, 0, x_769);
lean_ctor_set(x_781, 1, x_779);
x_782 = lean_array_push(x_778, x_781);
x_783 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_784 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_784, 0, x_756);
lean_ctor_set(x_784, 1, x_783);
x_785 = lean_array_push(x_782, x_784);
x_786 = lean_array_push(x_785, x_691);
x_787 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = lean_array_push(x_760, x_788);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_769);
lean_ctor_set(x_790, 1, x_789);
x_791 = lean_array_push(x_760, x_790);
x_792 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_791);
x_794 = lean_array_push(x_775, x_793);
x_795 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_794);
x_797 = 1;
x_798 = lean_box(x_797);
lean_ctor_set(x_686, 1, x_798);
lean_ctor_set(x_686, 0, x_796);
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_685);
lean_ctor_set(x_799, 1, x_757);
return x_799;
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_800 = lean_ctor_get(x_686, 0);
lean_inc(x_800);
lean_dec(x_686);
x_801 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_687);
lean_dec(x_5);
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
x_805 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_802);
x_806 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_806, 0, x_802);
lean_ctor_set(x_806, 1, x_805);
x_807 = l_Array_empty___closed__1;
x_808 = lean_array_push(x_807, x_806);
x_809 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_810 = lean_array_push(x_808, x_809);
x_811 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_812 = lean_array_push(x_811, x_677);
x_813 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
x_815 = lean_array_push(x_807, x_814);
x_816 = l_Lean_nullKind___closed__2;
x_817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_815);
x_818 = lean_array_push(x_810, x_817);
x_819 = lean_array_push(x_818, x_809);
x_820 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_802);
x_821 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_821, 0, x_802);
lean_ctor_set(x_821, 1, x_820);
x_822 = lean_array_push(x_819, x_821);
x_823 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_802);
x_824 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_824, 0, x_802);
lean_ctor_set(x_824, 1, x_823);
x_825 = lean_array_push(x_807, x_824);
lean_inc(x_14);
x_826 = lean_array_push(x_807, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_827 = x_14;
} else {
 lean_dec_ref(x_14);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_816);
lean_ctor_set(x_828, 1, x_826);
x_829 = lean_array_push(x_825, x_828);
x_830 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_831 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_831, 0, x_802);
lean_ctor_set(x_831, 1, x_830);
x_832 = lean_array_push(x_829, x_831);
x_833 = lean_array_push(x_832, x_800);
x_834 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_833);
x_836 = lean_array_push(x_807, x_835);
x_837 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_837, 0, x_816);
lean_ctor_set(x_837, 1, x_836);
x_838 = lean_array_push(x_807, x_837);
x_839 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_840, 0, x_839);
lean_ctor_set(x_840, 1, x_838);
x_841 = lean_array_push(x_822, x_840);
x_842 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_843 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_841);
x_844 = 1;
x_845 = lean_box(x_844);
x_846 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_845);
lean_ctor_set(x_685, 1, x_846);
if (lean_is_scalar(x_804)) {
 x_847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_847 = x_804;
}
lean_ctor_set(x_847, 0, x_685);
lean_ctor_set(x_847, 1, x_803);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_848 = lean_ctor_get(x_685, 0);
lean_inc(x_848);
lean_dec(x_685);
x_849 = lean_ctor_get(x_686, 0);
lean_inc(x_849);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_850 = x_686;
} else {
 lean_dec_ref(x_686);
 x_850 = lean_box(0);
}
x_851 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_687);
lean_dec(x_5);
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_854 = x_851;
} else {
 lean_dec_ref(x_851);
 x_854 = lean_box(0);
}
x_855 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_852);
x_856 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_856, 0, x_852);
lean_ctor_set(x_856, 1, x_855);
x_857 = l_Array_empty___closed__1;
x_858 = lean_array_push(x_857, x_856);
x_859 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_860 = lean_array_push(x_858, x_859);
x_861 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_862 = lean_array_push(x_861, x_677);
x_863 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_862);
x_865 = lean_array_push(x_857, x_864);
x_866 = l_Lean_nullKind___closed__2;
x_867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_867, 0, x_866);
lean_ctor_set(x_867, 1, x_865);
x_868 = lean_array_push(x_860, x_867);
x_869 = lean_array_push(x_868, x_859);
x_870 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_852);
x_871 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_871, 0, x_852);
lean_ctor_set(x_871, 1, x_870);
x_872 = lean_array_push(x_869, x_871);
x_873 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_852);
x_874 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_874, 0, x_852);
lean_ctor_set(x_874, 1, x_873);
x_875 = lean_array_push(x_857, x_874);
lean_inc(x_14);
x_876 = lean_array_push(x_857, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_877 = x_14;
} else {
 lean_dec_ref(x_14);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(1, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_866);
lean_ctor_set(x_878, 1, x_876);
x_879 = lean_array_push(x_875, x_878);
x_880 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_881 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_881, 0, x_852);
lean_ctor_set(x_881, 1, x_880);
x_882 = lean_array_push(x_879, x_881);
x_883 = lean_array_push(x_882, x_849);
x_884 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_885, 0, x_884);
lean_ctor_set(x_885, 1, x_883);
x_886 = lean_array_push(x_857, x_885);
x_887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_887, 0, x_866);
lean_ctor_set(x_887, 1, x_886);
x_888 = lean_array_push(x_857, x_887);
x_889 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_888);
x_891 = lean_array_push(x_872, x_890);
x_892 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_893, 0, x_892);
lean_ctor_set(x_893, 1, x_891);
x_894 = 1;
x_895 = lean_box(x_894);
if (lean_is_scalar(x_850)) {
 x_896 = lean_alloc_ctor(0, 2, 0);
} else {
 x_896 = x_850;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_895);
x_897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_897, 0, x_848);
lean_ctor_set(x_897, 1, x_896);
if (lean_is_scalar(x_854)) {
 x_898 = lean_alloc_ctor(0, 2, 0);
} else {
 x_898 = x_854;
}
lean_ctor_set(x_898, 0, x_897);
lean_ctor_set(x_898, 1, x_853);
return x_898;
}
}
else
{
lean_object* x_899; uint8_t x_900; 
x_899 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___lambda__2___closed__2;
x_900 = lean_string_dec_eq(x_220, x_899);
if (x_900 == 0)
{
lean_object* x_901; uint8_t x_902; 
x_901 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__2;
x_902 = lean_string_dec_eq(x_220, x_901);
if (x_902 == 0)
{
lean_object* x_903; uint8_t x_904; 
x_903 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5711____spec__3___closed__1;
x_904 = lean_string_dec_eq(x_220, x_903);
if (x_904 == 0)
{
lean_object* x_905; uint8_t x_906; 
x_905 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_906 = lean_string_dec_eq(x_220, x_905);
if (x_906 == 0)
{
lean_object* x_907; uint8_t x_908; 
x_907 = l_myMacro____x40_Init_Notation___hyg_15342____closed__12;
x_908 = lean_string_dec_eq(x_220, x_907);
if (x_908 == 0)
{
lean_object* x_909; uint8_t x_910; 
x_909 = l_myMacro____x40_Init_Notation___hyg_14734____closed__7;
x_910 = lean_string_dec_eq(x_220, x_909);
lean_dec(x_220);
if (x_910 == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; uint8_t x_923; 
lean_inc(x_5);
x_911 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_911, 1);
lean_inc(x_913);
lean_dec(x_911);
x_914 = lean_unsigned_to_nat(1u);
x_915 = lean_nat_add(x_3, x_914);
lean_dec(x_3);
x_916 = l_Lean_mkHole(x_14);
lean_inc(x_912);
x_917 = l_Lean_Elab_Term_mkExplicitBinder(x_912, x_916);
x_918 = lean_array_push(x_4, x_917);
lean_inc(x_5);
x_919 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_915, x_918, x_5, x_913);
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_920, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_919, 1);
lean_inc(x_922);
lean_dec(x_919);
x_923 = !lean_is_exclusive(x_920);
if (x_923 == 0)
{
lean_object* x_924; uint8_t x_925; 
x_924 = lean_ctor_get(x_920, 1);
lean_dec(x_924);
x_925 = !lean_is_exclusive(x_921);
if (x_925 == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; uint8_t x_929; 
x_926 = lean_ctor_get(x_921, 0);
x_927 = lean_ctor_get(x_921, 1);
lean_dec(x_927);
x_928 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_922);
lean_dec(x_5);
x_929 = !lean_is_exclusive(x_928);
if (x_929 == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; uint8_t x_953; 
x_930 = lean_ctor_get(x_928, 0);
x_931 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_930);
x_932 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_931);
x_933 = l_Array_empty___closed__1;
x_934 = lean_array_push(x_933, x_932);
x_935 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_936 = lean_array_push(x_934, x_935);
x_937 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_938 = lean_array_push(x_937, x_912);
x_939 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_940, 0, x_939);
lean_ctor_set(x_940, 1, x_938);
x_941 = lean_array_push(x_933, x_940);
x_942 = l_Lean_nullKind___closed__2;
x_943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_943, 0, x_942);
lean_ctor_set(x_943, 1, x_941);
x_944 = lean_array_push(x_936, x_943);
x_945 = lean_array_push(x_944, x_935);
x_946 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_930);
x_947 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_947, 0, x_930);
lean_ctor_set(x_947, 1, x_946);
x_948 = lean_array_push(x_945, x_947);
x_949 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_930);
x_950 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_950, 0, x_930);
lean_ctor_set(x_950, 1, x_949);
x_951 = lean_array_push(x_933, x_950);
lean_inc(x_14);
x_952 = lean_array_push(x_933, x_14);
x_953 = !lean_is_exclusive(x_14);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; uint8_t x_971; lean_object* x_972; 
x_954 = lean_ctor_get(x_14, 1);
lean_dec(x_954);
x_955 = lean_ctor_get(x_14, 0);
lean_dec(x_955);
lean_ctor_set(x_14, 1, x_952);
lean_ctor_set(x_14, 0, x_942);
x_956 = lean_array_push(x_951, x_14);
x_957 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_958 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_958, 0, x_930);
lean_ctor_set(x_958, 1, x_957);
x_959 = lean_array_push(x_956, x_958);
x_960 = lean_array_push(x_959, x_926);
x_961 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_962 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_962, 0, x_961);
lean_ctor_set(x_962, 1, x_960);
x_963 = lean_array_push(x_933, x_962);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_942);
lean_ctor_set(x_964, 1, x_963);
x_965 = lean_array_push(x_933, x_964);
x_966 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_967, 0, x_966);
lean_ctor_set(x_967, 1, x_965);
x_968 = lean_array_push(x_948, x_967);
x_969 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_970 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_968);
x_971 = 1;
x_972 = lean_box(x_971);
lean_ctor_set(x_921, 1, x_972);
lean_ctor_set(x_921, 0, x_970);
lean_ctor_set(x_928, 0, x_920);
return x_928;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; uint8_t x_989; lean_object* x_990; 
lean_dec(x_14);
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_942);
lean_ctor_set(x_973, 1, x_952);
x_974 = lean_array_push(x_951, x_973);
x_975 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_976 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_976, 0, x_930);
lean_ctor_set(x_976, 1, x_975);
x_977 = lean_array_push(x_974, x_976);
x_978 = lean_array_push(x_977, x_926);
x_979 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_978);
x_981 = lean_array_push(x_933, x_980);
x_982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_982, 0, x_942);
lean_ctor_set(x_982, 1, x_981);
x_983 = lean_array_push(x_933, x_982);
x_984 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_985 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_983);
x_986 = lean_array_push(x_948, x_985);
x_987 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_988, 0, x_987);
lean_ctor_set(x_988, 1, x_986);
x_989 = 1;
x_990 = lean_box(x_989);
lean_ctor_set(x_921, 1, x_990);
lean_ctor_set(x_921, 0, x_988);
lean_ctor_set(x_928, 0, x_920);
return x_928;
}
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; uint8_t x_1032; lean_object* x_1033; lean_object* x_1034; 
x_991 = lean_ctor_get(x_928, 0);
x_992 = lean_ctor_get(x_928, 1);
lean_inc(x_992);
lean_inc(x_991);
lean_dec(x_928);
x_993 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_991);
x_994 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_994, 0, x_991);
lean_ctor_set(x_994, 1, x_993);
x_995 = l_Array_empty___closed__1;
x_996 = lean_array_push(x_995, x_994);
x_997 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_998 = lean_array_push(x_996, x_997);
x_999 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1000 = lean_array_push(x_999, x_912);
x_1001 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_1000);
x_1003 = lean_array_push(x_995, x_1002);
x_1004 = l_Lean_nullKind___closed__2;
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_1003);
x_1006 = lean_array_push(x_998, x_1005);
x_1007 = lean_array_push(x_1006, x_997);
x_1008 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_991);
x_1009 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1009, 0, x_991);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = lean_array_push(x_1007, x_1009);
x_1011 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_991);
x_1012 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1012, 0, x_991);
lean_ctor_set(x_1012, 1, x_1011);
x_1013 = lean_array_push(x_995, x_1012);
lean_inc(x_14);
x_1014 = lean_array_push(x_995, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1015 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1004);
lean_ctor_set(x_1016, 1, x_1014);
x_1017 = lean_array_push(x_1013, x_1016);
x_1018 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1019 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1019, 0, x_991);
lean_ctor_set(x_1019, 1, x_1018);
x_1020 = lean_array_push(x_1017, x_1019);
x_1021 = lean_array_push(x_1020, x_926);
x_1022 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
x_1024 = lean_array_push(x_995, x_1023);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1004);
lean_ctor_set(x_1025, 1, x_1024);
x_1026 = lean_array_push(x_995, x_1025);
x_1027 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1027);
lean_ctor_set(x_1028, 1, x_1026);
x_1029 = lean_array_push(x_1010, x_1028);
x_1030 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1030);
lean_ctor_set(x_1031, 1, x_1029);
x_1032 = 1;
x_1033 = lean_box(x_1032);
lean_ctor_set(x_921, 1, x_1033);
lean_ctor_set(x_921, 0, x_1031);
x_1034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1034, 0, x_920);
lean_ctor_set(x_1034, 1, x_992);
return x_1034;
}
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1035 = lean_ctor_get(x_921, 0);
lean_inc(x_1035);
lean_dec(x_921);
x_1036 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_922);
lean_dec(x_5);
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1039 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1039 = lean_box(0);
}
x_1040 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1037);
x_1041 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1041, 0, x_1037);
lean_ctor_set(x_1041, 1, x_1040);
x_1042 = l_Array_empty___closed__1;
x_1043 = lean_array_push(x_1042, x_1041);
x_1044 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1045 = lean_array_push(x_1043, x_1044);
x_1046 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1047 = lean_array_push(x_1046, x_912);
x_1048 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1049 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_1047);
x_1050 = lean_array_push(x_1042, x_1049);
x_1051 = l_Lean_nullKind___closed__2;
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1050);
x_1053 = lean_array_push(x_1045, x_1052);
x_1054 = lean_array_push(x_1053, x_1044);
x_1055 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1037);
x_1056 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1056, 0, x_1037);
lean_ctor_set(x_1056, 1, x_1055);
x_1057 = lean_array_push(x_1054, x_1056);
x_1058 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1037);
x_1059 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1059, 0, x_1037);
lean_ctor_set(x_1059, 1, x_1058);
x_1060 = lean_array_push(x_1042, x_1059);
lean_inc(x_14);
x_1061 = lean_array_push(x_1042, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1062 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1062 = lean_box(0);
}
if (lean_is_scalar(x_1062)) {
 x_1063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1063 = x_1062;
}
lean_ctor_set(x_1063, 0, x_1051);
lean_ctor_set(x_1063, 1, x_1061);
x_1064 = lean_array_push(x_1060, x_1063);
x_1065 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1066 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1066, 0, x_1037);
lean_ctor_set(x_1066, 1, x_1065);
x_1067 = lean_array_push(x_1064, x_1066);
x_1068 = lean_array_push(x_1067, x_1035);
x_1069 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1070 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1068);
x_1071 = lean_array_push(x_1042, x_1070);
x_1072 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1072, 0, x_1051);
lean_ctor_set(x_1072, 1, x_1071);
x_1073 = lean_array_push(x_1042, x_1072);
x_1074 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1075 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1073);
x_1076 = lean_array_push(x_1057, x_1075);
x_1077 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1078 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1078, 0, x_1077);
lean_ctor_set(x_1078, 1, x_1076);
x_1079 = 1;
x_1080 = lean_box(x_1079);
x_1081 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1081, 0, x_1078);
lean_ctor_set(x_1081, 1, x_1080);
lean_ctor_set(x_920, 1, x_1081);
if (lean_is_scalar(x_1039)) {
 x_1082 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1082 = x_1039;
}
lean_ctor_set(x_1082, 0, x_920);
lean_ctor_set(x_1082, 1, x_1038);
return x_1082;
}
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1083 = lean_ctor_get(x_920, 0);
lean_inc(x_1083);
lean_dec(x_920);
x_1084 = lean_ctor_get(x_921, 0);
lean_inc(x_1084);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_1085 = x_921;
} else {
 lean_dec_ref(x_921);
 x_1085 = lean_box(0);
}
x_1086 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_922);
lean_dec(x_5);
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1089 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1089 = lean_box(0);
}
x_1090 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1087);
x_1091 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1091, 0, x_1087);
lean_ctor_set(x_1091, 1, x_1090);
x_1092 = l_Array_empty___closed__1;
x_1093 = lean_array_push(x_1092, x_1091);
x_1094 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1095 = lean_array_push(x_1093, x_1094);
x_1096 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1097 = lean_array_push(x_1096, x_912);
x_1098 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_1098);
lean_ctor_set(x_1099, 1, x_1097);
x_1100 = lean_array_push(x_1092, x_1099);
x_1101 = l_Lean_nullKind___closed__2;
x_1102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1100);
x_1103 = lean_array_push(x_1095, x_1102);
x_1104 = lean_array_push(x_1103, x_1094);
x_1105 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1087);
x_1106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1106, 0, x_1087);
lean_ctor_set(x_1106, 1, x_1105);
x_1107 = lean_array_push(x_1104, x_1106);
x_1108 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1087);
x_1109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1109, 0, x_1087);
lean_ctor_set(x_1109, 1, x_1108);
x_1110 = lean_array_push(x_1092, x_1109);
lean_inc(x_14);
x_1111 = lean_array_push(x_1092, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1112 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1112 = lean_box(0);
}
if (lean_is_scalar(x_1112)) {
 x_1113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1113 = x_1112;
}
lean_ctor_set(x_1113, 0, x_1101);
lean_ctor_set(x_1113, 1, x_1111);
x_1114 = lean_array_push(x_1110, x_1113);
x_1115 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1116, 0, x_1087);
lean_ctor_set(x_1116, 1, x_1115);
x_1117 = lean_array_push(x_1114, x_1116);
x_1118 = lean_array_push(x_1117, x_1084);
x_1119 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1120, 1, x_1118);
x_1121 = lean_array_push(x_1092, x_1120);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1101);
lean_ctor_set(x_1122, 1, x_1121);
x_1123 = lean_array_push(x_1092, x_1122);
x_1124 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1124);
lean_ctor_set(x_1125, 1, x_1123);
x_1126 = lean_array_push(x_1107, x_1125);
x_1127 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1127);
lean_ctor_set(x_1128, 1, x_1126);
x_1129 = 1;
x_1130 = lean_box(x_1129);
if (lean_is_scalar(x_1085)) {
 x_1131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1131 = x_1085;
}
lean_ctor_set(x_1131, 0, x_1128);
lean_ctor_set(x_1131, 1, x_1130);
x_1132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1132, 0, x_1083);
lean_ctor_set(x_1132, 1, x_1131);
if (lean_is_scalar(x_1089)) {
 x_1133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1133 = x_1089;
}
lean_ctor_set(x_1133, 0, x_1132);
lean_ctor_set(x_1133, 1, x_1088);
return x_1133;
}
}
else
{
lean_object* x_1134; lean_object* x_1135; uint8_t x_1136; 
x_1134 = lean_unsigned_to_nat(1u);
x_1135 = l_Lean_Syntax_getArg(x_14, x_1134);
x_1136 = l_Lean_Syntax_isNone(x_1135);
if (x_1136 == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; uint8_t x_1140; 
x_1137 = lean_unsigned_to_nat(0u);
x_1138 = l_Lean_Syntax_getArg(x_1135, x_1137);
x_1139 = l_Lean_Syntax_getArg(x_1135, x_1134);
lean_dec(x_1135);
x_1140 = l_Lean_Syntax_isNone(x_1139);
if (x_1140 == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; 
x_1141 = l_Lean_Syntax_getArg(x_1139, x_1137);
lean_dec(x_1139);
lean_inc(x_1141);
x_1142 = l_Lean_Syntax_getKind(x_1141);
x_1143 = l_myMacro____x40_Init_Notation___hyg_16268____closed__8;
x_1144 = lean_name_eq(x_1142, x_1143);
lean_dec(x_1142);
if (x_1144 == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; 
lean_dec(x_1141);
lean_dec(x_1138);
lean_inc(x_5);
x_1145 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_1146 = lean_ctor_get(x_1145, 0);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1145, 1);
lean_inc(x_1147);
lean_dec(x_1145);
x_1148 = lean_nat_add(x_3, x_1134);
lean_dec(x_3);
x_1149 = l_Lean_mkHole(x_14);
lean_inc(x_1146);
x_1150 = l_Lean_Elab_Term_mkExplicitBinder(x_1146, x_1149);
x_1151 = lean_array_push(x_4, x_1150);
lean_inc(x_5);
x_1152 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1148, x_1151, x_5, x_1147);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1153, 1);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1152, 1);
lean_inc(x_1155);
lean_dec(x_1152);
x_1156 = !lean_is_exclusive(x_1153);
if (x_1156 == 0)
{
lean_object* x_1157; uint8_t x_1158; 
x_1157 = lean_ctor_get(x_1153, 1);
lean_dec(x_1157);
x_1158 = !lean_is_exclusive(x_1154);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; uint8_t x_1162; 
x_1159 = lean_ctor_get(x_1154, 0);
x_1160 = lean_ctor_get(x_1154, 1);
lean_dec(x_1160);
x_1161 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1155);
lean_dec(x_5);
x_1162 = !lean_is_exclusive(x_1161);
if (x_1162 == 0)
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
x_1163 = lean_ctor_get(x_1161, 0);
x_1164 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1163);
x_1165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1165, 0, x_1163);
lean_ctor_set(x_1165, 1, x_1164);
x_1166 = l_Array_empty___closed__1;
x_1167 = lean_array_push(x_1166, x_1165);
x_1168 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1169 = lean_array_push(x_1167, x_1168);
x_1170 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1171 = lean_array_push(x_1170, x_1146);
x_1172 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1172);
lean_ctor_set(x_1173, 1, x_1171);
x_1174 = lean_array_push(x_1166, x_1173);
x_1175 = l_Lean_nullKind___closed__2;
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_1175);
lean_ctor_set(x_1176, 1, x_1174);
x_1177 = lean_array_push(x_1169, x_1176);
x_1178 = lean_array_push(x_1177, x_1168);
x_1179 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1163);
x_1180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1180, 0, x_1163);
lean_ctor_set(x_1180, 1, x_1179);
x_1181 = lean_array_push(x_1178, x_1180);
x_1182 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1163);
x_1183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1183, 0, x_1163);
lean_ctor_set(x_1183, 1, x_1182);
x_1184 = lean_array_push(x_1166, x_1183);
lean_inc(x_14);
x_1185 = lean_array_push(x_1166, x_14);
x_1186 = !lean_is_exclusive(x_14);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; lean_object* x_1205; 
x_1187 = lean_ctor_get(x_14, 1);
lean_dec(x_1187);
x_1188 = lean_ctor_get(x_14, 0);
lean_dec(x_1188);
lean_ctor_set(x_14, 1, x_1185);
lean_ctor_set(x_14, 0, x_1175);
x_1189 = lean_array_push(x_1184, x_14);
x_1190 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1191, 0, x_1163);
lean_ctor_set(x_1191, 1, x_1190);
x_1192 = lean_array_push(x_1189, x_1191);
x_1193 = lean_array_push(x_1192, x_1159);
x_1194 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1195, 0, x_1194);
lean_ctor_set(x_1195, 1, x_1193);
x_1196 = lean_array_push(x_1166, x_1195);
x_1197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1197, 0, x_1175);
lean_ctor_set(x_1197, 1, x_1196);
x_1198 = lean_array_push(x_1166, x_1197);
x_1199 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1200, 0, x_1199);
lean_ctor_set(x_1200, 1, x_1198);
x_1201 = lean_array_push(x_1181, x_1200);
x_1202 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1202);
lean_ctor_set(x_1203, 1, x_1201);
x_1204 = 1;
x_1205 = lean_box(x_1204);
lean_ctor_set(x_1154, 1, x_1205);
lean_ctor_set(x_1154, 0, x_1203);
lean_ctor_set(x_1161, 0, x_1153);
return x_1161;
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; lean_object* x_1223; 
lean_dec(x_14);
x_1206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1206, 0, x_1175);
lean_ctor_set(x_1206, 1, x_1185);
x_1207 = lean_array_push(x_1184, x_1206);
x_1208 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1209, 0, x_1163);
lean_ctor_set(x_1209, 1, x_1208);
x_1210 = lean_array_push(x_1207, x_1209);
x_1211 = lean_array_push(x_1210, x_1159);
x_1212 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1213, 0, x_1212);
lean_ctor_set(x_1213, 1, x_1211);
x_1214 = lean_array_push(x_1166, x_1213);
x_1215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1215, 0, x_1175);
lean_ctor_set(x_1215, 1, x_1214);
x_1216 = lean_array_push(x_1166, x_1215);
x_1217 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1217);
lean_ctor_set(x_1218, 1, x_1216);
x_1219 = lean_array_push(x_1181, x_1218);
x_1220 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = 1;
x_1223 = lean_box(x_1222);
lean_ctor_set(x_1154, 1, x_1223);
lean_ctor_set(x_1154, 0, x_1221);
lean_ctor_set(x_1161, 0, x_1153);
return x_1161;
}
}
else
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1224 = lean_ctor_get(x_1161, 0);
x_1225 = lean_ctor_get(x_1161, 1);
lean_inc(x_1225);
lean_inc(x_1224);
lean_dec(x_1161);
x_1226 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1224);
x_1227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1227, 0, x_1224);
lean_ctor_set(x_1227, 1, x_1226);
x_1228 = l_Array_empty___closed__1;
x_1229 = lean_array_push(x_1228, x_1227);
x_1230 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1231 = lean_array_push(x_1229, x_1230);
x_1232 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1233 = lean_array_push(x_1232, x_1146);
x_1234 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1233);
x_1236 = lean_array_push(x_1228, x_1235);
x_1237 = l_Lean_nullKind___closed__2;
x_1238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1238, 0, x_1237);
lean_ctor_set(x_1238, 1, x_1236);
x_1239 = lean_array_push(x_1231, x_1238);
x_1240 = lean_array_push(x_1239, x_1230);
x_1241 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1224);
x_1242 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1242, 0, x_1224);
lean_ctor_set(x_1242, 1, x_1241);
x_1243 = lean_array_push(x_1240, x_1242);
x_1244 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1224);
x_1245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1245, 0, x_1224);
lean_ctor_set(x_1245, 1, x_1244);
x_1246 = lean_array_push(x_1228, x_1245);
lean_inc(x_14);
x_1247 = lean_array_push(x_1228, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1248 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1248 = lean_box(0);
}
if (lean_is_scalar(x_1248)) {
 x_1249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1249 = x_1248;
}
lean_ctor_set(x_1249, 0, x_1237);
lean_ctor_set(x_1249, 1, x_1247);
x_1250 = lean_array_push(x_1246, x_1249);
x_1251 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1252, 0, x_1224);
lean_ctor_set(x_1252, 1, x_1251);
x_1253 = lean_array_push(x_1250, x_1252);
x_1254 = lean_array_push(x_1253, x_1159);
x_1255 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1256, 0, x_1255);
lean_ctor_set(x_1256, 1, x_1254);
x_1257 = lean_array_push(x_1228, x_1256);
x_1258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1258, 0, x_1237);
lean_ctor_set(x_1258, 1, x_1257);
x_1259 = lean_array_push(x_1228, x_1258);
x_1260 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1260);
lean_ctor_set(x_1261, 1, x_1259);
x_1262 = lean_array_push(x_1243, x_1261);
x_1263 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1264, 0, x_1263);
lean_ctor_set(x_1264, 1, x_1262);
x_1265 = 1;
x_1266 = lean_box(x_1265);
lean_ctor_set(x_1154, 1, x_1266);
lean_ctor_set(x_1154, 0, x_1264);
x_1267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1267, 0, x_1153);
lean_ctor_set(x_1267, 1, x_1225);
return x_1267;
}
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1268 = lean_ctor_get(x_1154, 0);
lean_inc(x_1268);
lean_dec(x_1154);
x_1269 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1155);
lean_dec(x_5);
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1269, 1);
lean_inc(x_1271);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1272 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1272 = lean_box(0);
}
x_1273 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1270);
x_1274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1274, 0, x_1270);
lean_ctor_set(x_1274, 1, x_1273);
x_1275 = l_Array_empty___closed__1;
x_1276 = lean_array_push(x_1275, x_1274);
x_1277 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1278 = lean_array_push(x_1276, x_1277);
x_1279 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1280 = lean_array_push(x_1279, x_1146);
x_1281 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1282, 0, x_1281);
lean_ctor_set(x_1282, 1, x_1280);
x_1283 = lean_array_push(x_1275, x_1282);
x_1284 = l_Lean_nullKind___closed__2;
x_1285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1285, 0, x_1284);
lean_ctor_set(x_1285, 1, x_1283);
x_1286 = lean_array_push(x_1278, x_1285);
x_1287 = lean_array_push(x_1286, x_1277);
x_1288 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1270);
x_1289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1289, 0, x_1270);
lean_ctor_set(x_1289, 1, x_1288);
x_1290 = lean_array_push(x_1287, x_1289);
x_1291 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1270);
x_1292 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1292, 0, x_1270);
lean_ctor_set(x_1292, 1, x_1291);
x_1293 = lean_array_push(x_1275, x_1292);
lean_inc(x_14);
x_1294 = lean_array_push(x_1275, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1295 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_1284);
lean_ctor_set(x_1296, 1, x_1294);
x_1297 = lean_array_push(x_1293, x_1296);
x_1298 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1299 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1299, 0, x_1270);
lean_ctor_set(x_1299, 1, x_1298);
x_1300 = lean_array_push(x_1297, x_1299);
x_1301 = lean_array_push(x_1300, x_1268);
x_1302 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1302);
lean_ctor_set(x_1303, 1, x_1301);
x_1304 = lean_array_push(x_1275, x_1303);
x_1305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1305, 0, x_1284);
lean_ctor_set(x_1305, 1, x_1304);
x_1306 = lean_array_push(x_1275, x_1305);
x_1307 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1308, 0, x_1307);
lean_ctor_set(x_1308, 1, x_1306);
x_1309 = lean_array_push(x_1290, x_1308);
x_1310 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1311, 0, x_1310);
lean_ctor_set(x_1311, 1, x_1309);
x_1312 = 1;
x_1313 = lean_box(x_1312);
x_1314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1314, 0, x_1311);
lean_ctor_set(x_1314, 1, x_1313);
lean_ctor_set(x_1153, 1, x_1314);
if (lean_is_scalar(x_1272)) {
 x_1315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1315 = x_1272;
}
lean_ctor_set(x_1315, 0, x_1153);
lean_ctor_set(x_1315, 1, x_1271);
return x_1315;
}
}
else
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; uint8_t x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1316 = lean_ctor_get(x_1153, 0);
lean_inc(x_1316);
lean_dec(x_1153);
x_1317 = lean_ctor_get(x_1154, 0);
lean_inc(x_1317);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1318 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1318 = lean_box(0);
}
x_1319 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1155);
lean_dec(x_5);
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1319, 1);
lean_inc(x_1321);
if (lean_is_exclusive(x_1319)) {
 lean_ctor_release(x_1319, 0);
 lean_ctor_release(x_1319, 1);
 x_1322 = x_1319;
} else {
 lean_dec_ref(x_1319);
 x_1322 = lean_box(0);
}
x_1323 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1320);
x_1324 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1324, 0, x_1320);
lean_ctor_set(x_1324, 1, x_1323);
x_1325 = l_Array_empty___closed__1;
x_1326 = lean_array_push(x_1325, x_1324);
x_1327 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1328 = lean_array_push(x_1326, x_1327);
x_1329 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1330 = lean_array_push(x_1329, x_1146);
x_1331 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1332, 0, x_1331);
lean_ctor_set(x_1332, 1, x_1330);
x_1333 = lean_array_push(x_1325, x_1332);
x_1334 = l_Lean_nullKind___closed__2;
x_1335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1335, 0, x_1334);
lean_ctor_set(x_1335, 1, x_1333);
x_1336 = lean_array_push(x_1328, x_1335);
x_1337 = lean_array_push(x_1336, x_1327);
x_1338 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1320);
x_1339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1339, 0, x_1320);
lean_ctor_set(x_1339, 1, x_1338);
x_1340 = lean_array_push(x_1337, x_1339);
x_1341 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1320);
x_1342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1342, 0, x_1320);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = lean_array_push(x_1325, x_1342);
lean_inc(x_14);
x_1344 = lean_array_push(x_1325, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1345 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1345 = lean_box(0);
}
if (lean_is_scalar(x_1345)) {
 x_1346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1346 = x_1345;
}
lean_ctor_set(x_1346, 0, x_1334);
lean_ctor_set(x_1346, 1, x_1344);
x_1347 = lean_array_push(x_1343, x_1346);
x_1348 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1349, 0, x_1320);
lean_ctor_set(x_1349, 1, x_1348);
x_1350 = lean_array_push(x_1347, x_1349);
x_1351 = lean_array_push(x_1350, x_1317);
x_1352 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1353, 0, x_1352);
lean_ctor_set(x_1353, 1, x_1351);
x_1354 = lean_array_push(x_1325, x_1353);
x_1355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1355, 0, x_1334);
lean_ctor_set(x_1355, 1, x_1354);
x_1356 = lean_array_push(x_1325, x_1355);
x_1357 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1358, 0, x_1357);
lean_ctor_set(x_1358, 1, x_1356);
x_1359 = lean_array_push(x_1340, x_1358);
x_1360 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1361, 0, x_1360);
lean_ctor_set(x_1361, 1, x_1359);
x_1362 = 1;
x_1363 = lean_box(x_1362);
if (lean_is_scalar(x_1318)) {
 x_1364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1364 = x_1318;
}
lean_ctor_set(x_1364, 0, x_1361);
lean_ctor_set(x_1364, 1, x_1363);
x_1365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1365, 0, x_1316);
lean_ctor_set(x_1365, 1, x_1364);
if (lean_is_scalar(x_1322)) {
 x_1366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1366 = x_1322;
}
lean_ctor_set(x_1366, 0, x_1365);
lean_ctor_set(x_1366, 1, x_1321);
return x_1366;
}
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = l_Lean_Syntax_getArg(x_1141, x_1134);
lean_dec(x_1141);
lean_inc(x_5);
x_1368 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_1138, x_5, x_6);
x_1369 = lean_ctor_get(x_1368, 0);
lean_inc(x_1369);
if (lean_obj_tag(x_1369) == 0)
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; uint8_t x_1382; 
lean_dec(x_1367);
x_1370 = lean_ctor_get(x_1368, 1);
lean_inc(x_1370);
lean_dec(x_1368);
lean_inc(x_5);
x_1371 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_1370);
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
lean_dec(x_1371);
x_1374 = lean_nat_add(x_3, x_1134);
lean_dec(x_3);
x_1375 = l_Lean_mkHole(x_14);
lean_inc(x_1372);
x_1376 = l_Lean_Elab_Term_mkExplicitBinder(x_1372, x_1375);
x_1377 = lean_array_push(x_4, x_1376);
lean_inc(x_5);
x_1378 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1374, x_1377, x_5, x_1373);
x_1379 = lean_ctor_get(x_1378, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1379, 1);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1378, 1);
lean_inc(x_1381);
lean_dec(x_1378);
x_1382 = !lean_is_exclusive(x_1379);
if (x_1382 == 0)
{
lean_object* x_1383; uint8_t x_1384; 
x_1383 = lean_ctor_get(x_1379, 1);
lean_dec(x_1383);
x_1384 = !lean_is_exclusive(x_1380);
if (x_1384 == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; uint8_t x_1388; 
x_1385 = lean_ctor_get(x_1380, 0);
x_1386 = lean_ctor_get(x_1380, 1);
lean_dec(x_1386);
x_1387 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1381);
lean_dec(x_5);
x_1388 = !lean_is_exclusive(x_1387);
if (x_1388 == 0)
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1412; 
x_1389 = lean_ctor_get(x_1387, 0);
x_1390 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1389);
x_1391 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1391, 0, x_1389);
lean_ctor_set(x_1391, 1, x_1390);
x_1392 = l_Array_empty___closed__1;
x_1393 = lean_array_push(x_1392, x_1391);
x_1394 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1395 = lean_array_push(x_1393, x_1394);
x_1396 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1397 = lean_array_push(x_1396, x_1372);
x_1398 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1399, 0, x_1398);
lean_ctor_set(x_1399, 1, x_1397);
x_1400 = lean_array_push(x_1392, x_1399);
x_1401 = l_Lean_nullKind___closed__2;
x_1402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1402, 0, x_1401);
lean_ctor_set(x_1402, 1, x_1400);
x_1403 = lean_array_push(x_1395, x_1402);
x_1404 = lean_array_push(x_1403, x_1394);
x_1405 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1389);
x_1406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1406, 0, x_1389);
lean_ctor_set(x_1406, 1, x_1405);
x_1407 = lean_array_push(x_1404, x_1406);
x_1408 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1389);
x_1409 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1409, 0, x_1389);
lean_ctor_set(x_1409, 1, x_1408);
x_1410 = lean_array_push(x_1392, x_1409);
lean_inc(x_14);
x_1411 = lean_array_push(x_1392, x_14);
x_1412 = !lean_is_exclusive(x_14);
if (x_1412 == 0)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; uint8_t x_1430; lean_object* x_1431; 
x_1413 = lean_ctor_get(x_14, 1);
lean_dec(x_1413);
x_1414 = lean_ctor_get(x_14, 0);
lean_dec(x_1414);
lean_ctor_set(x_14, 1, x_1411);
lean_ctor_set(x_14, 0, x_1401);
x_1415 = lean_array_push(x_1410, x_14);
x_1416 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1417 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1417, 0, x_1389);
lean_ctor_set(x_1417, 1, x_1416);
x_1418 = lean_array_push(x_1415, x_1417);
x_1419 = lean_array_push(x_1418, x_1385);
x_1420 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1421, 0, x_1420);
lean_ctor_set(x_1421, 1, x_1419);
x_1422 = lean_array_push(x_1392, x_1421);
x_1423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1423, 0, x_1401);
lean_ctor_set(x_1423, 1, x_1422);
x_1424 = lean_array_push(x_1392, x_1423);
x_1425 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1426, 0, x_1425);
lean_ctor_set(x_1426, 1, x_1424);
x_1427 = lean_array_push(x_1407, x_1426);
x_1428 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1429, 0, x_1428);
lean_ctor_set(x_1429, 1, x_1427);
x_1430 = 1;
x_1431 = lean_box(x_1430);
lean_ctor_set(x_1380, 1, x_1431);
lean_ctor_set(x_1380, 0, x_1429);
lean_ctor_set(x_1387, 0, x_1379);
return x_1387;
}
else
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; uint8_t x_1448; lean_object* x_1449; 
lean_dec(x_14);
x_1432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1432, 0, x_1401);
lean_ctor_set(x_1432, 1, x_1411);
x_1433 = lean_array_push(x_1410, x_1432);
x_1434 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1435 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1435, 0, x_1389);
lean_ctor_set(x_1435, 1, x_1434);
x_1436 = lean_array_push(x_1433, x_1435);
x_1437 = lean_array_push(x_1436, x_1385);
x_1438 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1439, 0, x_1438);
lean_ctor_set(x_1439, 1, x_1437);
x_1440 = lean_array_push(x_1392, x_1439);
x_1441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1441, 0, x_1401);
lean_ctor_set(x_1441, 1, x_1440);
x_1442 = lean_array_push(x_1392, x_1441);
x_1443 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1444, 0, x_1443);
lean_ctor_set(x_1444, 1, x_1442);
x_1445 = lean_array_push(x_1407, x_1444);
x_1446 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_1445);
x_1448 = 1;
x_1449 = lean_box(x_1448);
lean_ctor_set(x_1380, 1, x_1449);
lean_ctor_set(x_1380, 0, x_1447);
lean_ctor_set(x_1387, 0, x_1379);
return x_1387;
}
}
else
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; uint8_t x_1491; lean_object* x_1492; lean_object* x_1493; 
x_1450 = lean_ctor_get(x_1387, 0);
x_1451 = lean_ctor_get(x_1387, 1);
lean_inc(x_1451);
lean_inc(x_1450);
lean_dec(x_1387);
x_1452 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1450);
x_1453 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1453, 0, x_1450);
lean_ctor_set(x_1453, 1, x_1452);
x_1454 = l_Array_empty___closed__1;
x_1455 = lean_array_push(x_1454, x_1453);
x_1456 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1457 = lean_array_push(x_1455, x_1456);
x_1458 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1459 = lean_array_push(x_1458, x_1372);
x_1460 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1461, 0, x_1460);
lean_ctor_set(x_1461, 1, x_1459);
x_1462 = lean_array_push(x_1454, x_1461);
x_1463 = l_Lean_nullKind___closed__2;
x_1464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1464, 0, x_1463);
lean_ctor_set(x_1464, 1, x_1462);
x_1465 = lean_array_push(x_1457, x_1464);
x_1466 = lean_array_push(x_1465, x_1456);
x_1467 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1450);
x_1468 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1468, 0, x_1450);
lean_ctor_set(x_1468, 1, x_1467);
x_1469 = lean_array_push(x_1466, x_1468);
x_1470 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1450);
x_1471 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1471, 0, x_1450);
lean_ctor_set(x_1471, 1, x_1470);
x_1472 = lean_array_push(x_1454, x_1471);
lean_inc(x_14);
x_1473 = lean_array_push(x_1454, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1474 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1474 = lean_box(0);
}
if (lean_is_scalar(x_1474)) {
 x_1475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1475 = x_1474;
}
lean_ctor_set(x_1475, 0, x_1463);
lean_ctor_set(x_1475, 1, x_1473);
x_1476 = lean_array_push(x_1472, x_1475);
x_1477 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1478 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1478, 0, x_1450);
lean_ctor_set(x_1478, 1, x_1477);
x_1479 = lean_array_push(x_1476, x_1478);
x_1480 = lean_array_push(x_1479, x_1385);
x_1481 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1482, 0, x_1481);
lean_ctor_set(x_1482, 1, x_1480);
x_1483 = lean_array_push(x_1454, x_1482);
x_1484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1484, 0, x_1463);
lean_ctor_set(x_1484, 1, x_1483);
x_1485 = lean_array_push(x_1454, x_1484);
x_1486 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1487, 0, x_1486);
lean_ctor_set(x_1487, 1, x_1485);
x_1488 = lean_array_push(x_1469, x_1487);
x_1489 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1490, 0, x_1489);
lean_ctor_set(x_1490, 1, x_1488);
x_1491 = 1;
x_1492 = lean_box(x_1491);
lean_ctor_set(x_1380, 1, x_1492);
lean_ctor_set(x_1380, 0, x_1490);
x_1493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1493, 0, x_1379);
lean_ctor_set(x_1493, 1, x_1451);
return x_1493;
}
}
else
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; uint8_t x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
x_1494 = lean_ctor_get(x_1380, 0);
lean_inc(x_1494);
lean_dec(x_1380);
x_1495 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1381);
lean_dec(x_5);
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1495, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1495)) {
 lean_ctor_release(x_1495, 0);
 lean_ctor_release(x_1495, 1);
 x_1498 = x_1495;
} else {
 lean_dec_ref(x_1495);
 x_1498 = lean_box(0);
}
x_1499 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1496);
x_1500 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1500, 0, x_1496);
lean_ctor_set(x_1500, 1, x_1499);
x_1501 = l_Array_empty___closed__1;
x_1502 = lean_array_push(x_1501, x_1500);
x_1503 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1504 = lean_array_push(x_1502, x_1503);
x_1505 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1506 = lean_array_push(x_1505, x_1372);
x_1507 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1508, 0, x_1507);
lean_ctor_set(x_1508, 1, x_1506);
x_1509 = lean_array_push(x_1501, x_1508);
x_1510 = l_Lean_nullKind___closed__2;
x_1511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1511, 0, x_1510);
lean_ctor_set(x_1511, 1, x_1509);
x_1512 = lean_array_push(x_1504, x_1511);
x_1513 = lean_array_push(x_1512, x_1503);
x_1514 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1496);
x_1515 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1515, 0, x_1496);
lean_ctor_set(x_1515, 1, x_1514);
x_1516 = lean_array_push(x_1513, x_1515);
x_1517 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1496);
x_1518 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1518, 0, x_1496);
lean_ctor_set(x_1518, 1, x_1517);
x_1519 = lean_array_push(x_1501, x_1518);
lean_inc(x_14);
x_1520 = lean_array_push(x_1501, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1521 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1521 = lean_box(0);
}
if (lean_is_scalar(x_1521)) {
 x_1522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1522 = x_1521;
}
lean_ctor_set(x_1522, 0, x_1510);
lean_ctor_set(x_1522, 1, x_1520);
x_1523 = lean_array_push(x_1519, x_1522);
x_1524 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1525 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1525, 0, x_1496);
lean_ctor_set(x_1525, 1, x_1524);
x_1526 = lean_array_push(x_1523, x_1525);
x_1527 = lean_array_push(x_1526, x_1494);
x_1528 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1529, 0, x_1528);
lean_ctor_set(x_1529, 1, x_1527);
x_1530 = lean_array_push(x_1501, x_1529);
x_1531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1531, 0, x_1510);
lean_ctor_set(x_1531, 1, x_1530);
x_1532 = lean_array_push(x_1501, x_1531);
x_1533 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set(x_1534, 1, x_1532);
x_1535 = lean_array_push(x_1516, x_1534);
x_1536 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1537, 0, x_1536);
lean_ctor_set(x_1537, 1, x_1535);
x_1538 = 1;
x_1539 = lean_box(x_1538);
x_1540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1540, 0, x_1537);
lean_ctor_set(x_1540, 1, x_1539);
lean_ctor_set(x_1379, 1, x_1540);
if (lean_is_scalar(x_1498)) {
 x_1541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1541 = x_1498;
}
lean_ctor_set(x_1541, 0, x_1379);
lean_ctor_set(x_1541, 1, x_1497);
return x_1541;
}
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; uint8_t x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; 
x_1542 = lean_ctor_get(x_1379, 0);
lean_inc(x_1542);
lean_dec(x_1379);
x_1543 = lean_ctor_get(x_1380, 0);
lean_inc(x_1543);
if (lean_is_exclusive(x_1380)) {
 lean_ctor_release(x_1380, 0);
 lean_ctor_release(x_1380, 1);
 x_1544 = x_1380;
} else {
 lean_dec_ref(x_1380);
 x_1544 = lean_box(0);
}
x_1545 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1381);
lean_dec(x_5);
x_1546 = lean_ctor_get(x_1545, 0);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1545, 1);
lean_inc(x_1547);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 lean_ctor_release(x_1545, 1);
 x_1548 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1548 = lean_box(0);
}
x_1549 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1546);
x_1550 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1550, 0, x_1546);
lean_ctor_set(x_1550, 1, x_1549);
x_1551 = l_Array_empty___closed__1;
x_1552 = lean_array_push(x_1551, x_1550);
x_1553 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1554 = lean_array_push(x_1552, x_1553);
x_1555 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1556 = lean_array_push(x_1555, x_1372);
x_1557 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1558, 0, x_1557);
lean_ctor_set(x_1558, 1, x_1556);
x_1559 = lean_array_push(x_1551, x_1558);
x_1560 = l_Lean_nullKind___closed__2;
x_1561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1561, 0, x_1560);
lean_ctor_set(x_1561, 1, x_1559);
x_1562 = lean_array_push(x_1554, x_1561);
x_1563 = lean_array_push(x_1562, x_1553);
x_1564 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1546);
x_1565 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1565, 0, x_1546);
lean_ctor_set(x_1565, 1, x_1564);
x_1566 = lean_array_push(x_1563, x_1565);
x_1567 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1546);
x_1568 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1568, 0, x_1546);
lean_ctor_set(x_1568, 1, x_1567);
x_1569 = lean_array_push(x_1551, x_1568);
lean_inc(x_14);
x_1570 = lean_array_push(x_1551, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1571 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1571 = lean_box(0);
}
if (lean_is_scalar(x_1571)) {
 x_1572 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1572 = x_1571;
}
lean_ctor_set(x_1572, 0, x_1560);
lean_ctor_set(x_1572, 1, x_1570);
x_1573 = lean_array_push(x_1569, x_1572);
x_1574 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1575, 0, x_1546);
lean_ctor_set(x_1575, 1, x_1574);
x_1576 = lean_array_push(x_1573, x_1575);
x_1577 = lean_array_push(x_1576, x_1543);
x_1578 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1579, 0, x_1578);
lean_ctor_set(x_1579, 1, x_1577);
x_1580 = lean_array_push(x_1551, x_1579);
x_1581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1581, 0, x_1560);
lean_ctor_set(x_1581, 1, x_1580);
x_1582 = lean_array_push(x_1551, x_1581);
x_1583 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1584, 0, x_1583);
lean_ctor_set(x_1584, 1, x_1582);
x_1585 = lean_array_push(x_1566, x_1584);
x_1586 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1587, 0, x_1586);
lean_ctor_set(x_1587, 1, x_1585);
x_1588 = 1;
x_1589 = lean_box(x_1588);
if (lean_is_scalar(x_1544)) {
 x_1590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1590 = x_1544;
}
lean_ctor_set(x_1590, 0, x_1587);
lean_ctor_set(x_1590, 1, x_1589);
x_1591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1591, 0, x_1542);
lean_ctor_set(x_1591, 1, x_1590);
if (lean_is_scalar(x_1548)) {
 x_1592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1592 = x_1548;
}
lean_ctor_set(x_1592, 0, x_1591);
lean_ctor_set(x_1592, 1, x_1547);
return x_1592;
}
}
else
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; size_t x_1597; size_t x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; 
lean_dec(x_14);
x_1593 = lean_ctor_get(x_1368, 1);
lean_inc(x_1593);
lean_dec(x_1368);
x_1594 = lean_ctor_get(x_1369, 0);
lean_inc(x_1594);
lean_dec(x_1369);
x_1595 = lean_nat_add(x_3, x_1134);
lean_dec(x_3);
x_1596 = lean_array_get_size(x_1594);
x_1597 = lean_usize_of_nat(x_1596);
lean_dec(x_1596);
x_1598 = 0;
x_1599 = x_1594;
x_1600 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(x_1367, x_1597, x_1598, x_1599);
x_1601 = x_1600;
x_1602 = l_Array_append___rarg(x_4, x_1601);
lean_dec(x_1601);
x_3 = x_1595;
x_4 = x_1602;
x_6 = x_1593;
goto _start;
}
}
}
else
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; uint8_t x_1615; 
lean_dec(x_1139);
lean_dec(x_1138);
lean_inc(x_5);
x_1604 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_1605 = lean_ctor_get(x_1604, 0);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1604, 1);
lean_inc(x_1606);
lean_dec(x_1604);
x_1607 = lean_nat_add(x_3, x_1134);
lean_dec(x_3);
x_1608 = l_Lean_mkHole(x_14);
lean_inc(x_1605);
x_1609 = l_Lean_Elab_Term_mkExplicitBinder(x_1605, x_1608);
x_1610 = lean_array_push(x_4, x_1609);
lean_inc(x_5);
x_1611 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1607, x_1610, x_5, x_1606);
x_1612 = lean_ctor_get(x_1611, 0);
lean_inc(x_1612);
x_1613 = lean_ctor_get(x_1612, 1);
lean_inc(x_1613);
x_1614 = lean_ctor_get(x_1611, 1);
lean_inc(x_1614);
lean_dec(x_1611);
x_1615 = !lean_is_exclusive(x_1612);
if (x_1615 == 0)
{
lean_object* x_1616; uint8_t x_1617; 
x_1616 = lean_ctor_get(x_1612, 1);
lean_dec(x_1616);
x_1617 = !lean_is_exclusive(x_1613);
if (x_1617 == 0)
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; uint8_t x_1621; 
x_1618 = lean_ctor_get(x_1613, 0);
x_1619 = lean_ctor_get(x_1613, 1);
lean_dec(x_1619);
x_1620 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1614);
lean_dec(x_5);
x_1621 = !lean_is_exclusive(x_1620);
if (x_1621 == 0)
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; uint8_t x_1645; 
x_1622 = lean_ctor_get(x_1620, 0);
x_1623 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1622);
x_1624 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1624, 0, x_1622);
lean_ctor_set(x_1624, 1, x_1623);
x_1625 = l_Array_empty___closed__1;
x_1626 = lean_array_push(x_1625, x_1624);
x_1627 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1628 = lean_array_push(x_1626, x_1627);
x_1629 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1630 = lean_array_push(x_1629, x_1605);
x_1631 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1632, 0, x_1631);
lean_ctor_set(x_1632, 1, x_1630);
x_1633 = lean_array_push(x_1625, x_1632);
x_1634 = l_Lean_nullKind___closed__2;
x_1635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1635, 0, x_1634);
lean_ctor_set(x_1635, 1, x_1633);
x_1636 = lean_array_push(x_1628, x_1635);
x_1637 = lean_array_push(x_1636, x_1627);
x_1638 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1622);
x_1639 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1639, 0, x_1622);
lean_ctor_set(x_1639, 1, x_1638);
x_1640 = lean_array_push(x_1637, x_1639);
x_1641 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1622);
x_1642 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1642, 0, x_1622);
lean_ctor_set(x_1642, 1, x_1641);
x_1643 = lean_array_push(x_1625, x_1642);
lean_inc(x_14);
x_1644 = lean_array_push(x_1625, x_14);
x_1645 = !lean_is_exclusive(x_14);
if (x_1645 == 0)
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; uint8_t x_1663; lean_object* x_1664; 
x_1646 = lean_ctor_get(x_14, 1);
lean_dec(x_1646);
x_1647 = lean_ctor_get(x_14, 0);
lean_dec(x_1647);
lean_ctor_set(x_14, 1, x_1644);
lean_ctor_set(x_14, 0, x_1634);
x_1648 = lean_array_push(x_1643, x_14);
x_1649 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1650 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1650, 0, x_1622);
lean_ctor_set(x_1650, 1, x_1649);
x_1651 = lean_array_push(x_1648, x_1650);
x_1652 = lean_array_push(x_1651, x_1618);
x_1653 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1654, 0, x_1653);
lean_ctor_set(x_1654, 1, x_1652);
x_1655 = lean_array_push(x_1625, x_1654);
x_1656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1656, 0, x_1634);
lean_ctor_set(x_1656, 1, x_1655);
x_1657 = lean_array_push(x_1625, x_1656);
x_1658 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1659, 0, x_1658);
lean_ctor_set(x_1659, 1, x_1657);
x_1660 = lean_array_push(x_1640, x_1659);
x_1661 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1662, 0, x_1661);
lean_ctor_set(x_1662, 1, x_1660);
x_1663 = 1;
x_1664 = lean_box(x_1663);
lean_ctor_set(x_1613, 1, x_1664);
lean_ctor_set(x_1613, 0, x_1662);
lean_ctor_set(x_1620, 0, x_1612);
return x_1620;
}
else
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; uint8_t x_1681; lean_object* x_1682; 
lean_dec(x_14);
x_1665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1665, 0, x_1634);
lean_ctor_set(x_1665, 1, x_1644);
x_1666 = lean_array_push(x_1643, x_1665);
x_1667 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1668 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1668, 0, x_1622);
lean_ctor_set(x_1668, 1, x_1667);
x_1669 = lean_array_push(x_1666, x_1668);
x_1670 = lean_array_push(x_1669, x_1618);
x_1671 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1672, 0, x_1671);
lean_ctor_set(x_1672, 1, x_1670);
x_1673 = lean_array_push(x_1625, x_1672);
x_1674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1674, 0, x_1634);
lean_ctor_set(x_1674, 1, x_1673);
x_1675 = lean_array_push(x_1625, x_1674);
x_1676 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1677, 0, x_1676);
lean_ctor_set(x_1677, 1, x_1675);
x_1678 = lean_array_push(x_1640, x_1677);
x_1679 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1680, 0, x_1679);
lean_ctor_set(x_1680, 1, x_1678);
x_1681 = 1;
x_1682 = lean_box(x_1681);
lean_ctor_set(x_1613, 1, x_1682);
lean_ctor_set(x_1613, 0, x_1680);
lean_ctor_set(x_1620, 0, x_1612);
return x_1620;
}
}
else
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; uint8_t x_1724; lean_object* x_1725; lean_object* x_1726; 
x_1683 = lean_ctor_get(x_1620, 0);
x_1684 = lean_ctor_get(x_1620, 1);
lean_inc(x_1684);
lean_inc(x_1683);
lean_dec(x_1620);
x_1685 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1683);
x_1686 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1686, 0, x_1683);
lean_ctor_set(x_1686, 1, x_1685);
x_1687 = l_Array_empty___closed__1;
x_1688 = lean_array_push(x_1687, x_1686);
x_1689 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1690 = lean_array_push(x_1688, x_1689);
x_1691 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1692 = lean_array_push(x_1691, x_1605);
x_1693 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1694, 0, x_1693);
lean_ctor_set(x_1694, 1, x_1692);
x_1695 = lean_array_push(x_1687, x_1694);
x_1696 = l_Lean_nullKind___closed__2;
x_1697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1697, 0, x_1696);
lean_ctor_set(x_1697, 1, x_1695);
x_1698 = lean_array_push(x_1690, x_1697);
x_1699 = lean_array_push(x_1698, x_1689);
x_1700 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1683);
x_1701 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1701, 0, x_1683);
lean_ctor_set(x_1701, 1, x_1700);
x_1702 = lean_array_push(x_1699, x_1701);
x_1703 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1683);
x_1704 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1704, 0, x_1683);
lean_ctor_set(x_1704, 1, x_1703);
x_1705 = lean_array_push(x_1687, x_1704);
lean_inc(x_14);
x_1706 = lean_array_push(x_1687, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1707 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1707 = lean_box(0);
}
if (lean_is_scalar(x_1707)) {
 x_1708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1708 = x_1707;
}
lean_ctor_set(x_1708, 0, x_1696);
lean_ctor_set(x_1708, 1, x_1706);
x_1709 = lean_array_push(x_1705, x_1708);
x_1710 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1711 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1711, 0, x_1683);
lean_ctor_set(x_1711, 1, x_1710);
x_1712 = lean_array_push(x_1709, x_1711);
x_1713 = lean_array_push(x_1712, x_1618);
x_1714 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1715, 0, x_1714);
lean_ctor_set(x_1715, 1, x_1713);
x_1716 = lean_array_push(x_1687, x_1715);
x_1717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1717, 0, x_1696);
lean_ctor_set(x_1717, 1, x_1716);
x_1718 = lean_array_push(x_1687, x_1717);
x_1719 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1720, 0, x_1719);
lean_ctor_set(x_1720, 1, x_1718);
x_1721 = lean_array_push(x_1702, x_1720);
x_1722 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1723, 0, x_1722);
lean_ctor_set(x_1723, 1, x_1721);
x_1724 = 1;
x_1725 = lean_box(x_1724);
lean_ctor_set(x_1613, 1, x_1725);
lean_ctor_set(x_1613, 0, x_1723);
x_1726 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1726, 0, x_1612);
lean_ctor_set(x_1726, 1, x_1684);
return x_1726;
}
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; uint8_t x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
x_1727 = lean_ctor_get(x_1613, 0);
lean_inc(x_1727);
lean_dec(x_1613);
x_1728 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1614);
lean_dec(x_5);
x_1729 = lean_ctor_get(x_1728, 0);
lean_inc(x_1729);
x_1730 = lean_ctor_get(x_1728, 1);
lean_inc(x_1730);
if (lean_is_exclusive(x_1728)) {
 lean_ctor_release(x_1728, 0);
 lean_ctor_release(x_1728, 1);
 x_1731 = x_1728;
} else {
 lean_dec_ref(x_1728);
 x_1731 = lean_box(0);
}
x_1732 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1729);
x_1733 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1733, 0, x_1729);
lean_ctor_set(x_1733, 1, x_1732);
x_1734 = l_Array_empty___closed__1;
x_1735 = lean_array_push(x_1734, x_1733);
x_1736 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1737 = lean_array_push(x_1735, x_1736);
x_1738 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1739 = lean_array_push(x_1738, x_1605);
x_1740 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1741, 0, x_1740);
lean_ctor_set(x_1741, 1, x_1739);
x_1742 = lean_array_push(x_1734, x_1741);
x_1743 = l_Lean_nullKind___closed__2;
x_1744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1744, 0, x_1743);
lean_ctor_set(x_1744, 1, x_1742);
x_1745 = lean_array_push(x_1737, x_1744);
x_1746 = lean_array_push(x_1745, x_1736);
x_1747 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1729);
x_1748 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1748, 0, x_1729);
lean_ctor_set(x_1748, 1, x_1747);
x_1749 = lean_array_push(x_1746, x_1748);
x_1750 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1729);
x_1751 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1751, 0, x_1729);
lean_ctor_set(x_1751, 1, x_1750);
x_1752 = lean_array_push(x_1734, x_1751);
lean_inc(x_14);
x_1753 = lean_array_push(x_1734, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1754 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1754 = lean_box(0);
}
if (lean_is_scalar(x_1754)) {
 x_1755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1755 = x_1754;
}
lean_ctor_set(x_1755, 0, x_1743);
lean_ctor_set(x_1755, 1, x_1753);
x_1756 = lean_array_push(x_1752, x_1755);
x_1757 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1758 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1758, 0, x_1729);
lean_ctor_set(x_1758, 1, x_1757);
x_1759 = lean_array_push(x_1756, x_1758);
x_1760 = lean_array_push(x_1759, x_1727);
x_1761 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1762, 0, x_1761);
lean_ctor_set(x_1762, 1, x_1760);
x_1763 = lean_array_push(x_1734, x_1762);
x_1764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1764, 0, x_1743);
lean_ctor_set(x_1764, 1, x_1763);
x_1765 = lean_array_push(x_1734, x_1764);
x_1766 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1767, 0, x_1766);
lean_ctor_set(x_1767, 1, x_1765);
x_1768 = lean_array_push(x_1749, x_1767);
x_1769 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1770, 0, x_1769);
lean_ctor_set(x_1770, 1, x_1768);
x_1771 = 1;
x_1772 = lean_box(x_1771);
x_1773 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1773, 0, x_1770);
lean_ctor_set(x_1773, 1, x_1772);
lean_ctor_set(x_1612, 1, x_1773);
if (lean_is_scalar(x_1731)) {
 x_1774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1774 = x_1731;
}
lean_ctor_set(x_1774, 0, x_1612);
lean_ctor_set(x_1774, 1, x_1730);
return x_1774;
}
}
else
{
lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; uint8_t x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; 
x_1775 = lean_ctor_get(x_1612, 0);
lean_inc(x_1775);
lean_dec(x_1612);
x_1776 = lean_ctor_get(x_1613, 0);
lean_inc(x_1776);
if (lean_is_exclusive(x_1613)) {
 lean_ctor_release(x_1613, 0);
 lean_ctor_release(x_1613, 1);
 x_1777 = x_1613;
} else {
 lean_dec_ref(x_1613);
 x_1777 = lean_box(0);
}
x_1778 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1614);
lean_dec(x_5);
x_1779 = lean_ctor_get(x_1778, 0);
lean_inc(x_1779);
x_1780 = lean_ctor_get(x_1778, 1);
lean_inc(x_1780);
if (lean_is_exclusive(x_1778)) {
 lean_ctor_release(x_1778, 0);
 lean_ctor_release(x_1778, 1);
 x_1781 = x_1778;
} else {
 lean_dec_ref(x_1778);
 x_1781 = lean_box(0);
}
x_1782 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1779);
x_1783 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1783, 0, x_1779);
lean_ctor_set(x_1783, 1, x_1782);
x_1784 = l_Array_empty___closed__1;
x_1785 = lean_array_push(x_1784, x_1783);
x_1786 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1787 = lean_array_push(x_1785, x_1786);
x_1788 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1789 = lean_array_push(x_1788, x_1605);
x_1790 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1791, 0, x_1790);
lean_ctor_set(x_1791, 1, x_1789);
x_1792 = lean_array_push(x_1784, x_1791);
x_1793 = l_Lean_nullKind___closed__2;
x_1794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1794, 0, x_1793);
lean_ctor_set(x_1794, 1, x_1792);
x_1795 = lean_array_push(x_1787, x_1794);
x_1796 = lean_array_push(x_1795, x_1786);
x_1797 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1779);
x_1798 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1798, 0, x_1779);
lean_ctor_set(x_1798, 1, x_1797);
x_1799 = lean_array_push(x_1796, x_1798);
x_1800 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1779);
x_1801 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1801, 0, x_1779);
lean_ctor_set(x_1801, 1, x_1800);
x_1802 = lean_array_push(x_1784, x_1801);
lean_inc(x_14);
x_1803 = lean_array_push(x_1784, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1804 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1804 = lean_box(0);
}
if (lean_is_scalar(x_1804)) {
 x_1805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1805 = x_1804;
}
lean_ctor_set(x_1805, 0, x_1793);
lean_ctor_set(x_1805, 1, x_1803);
x_1806 = lean_array_push(x_1802, x_1805);
x_1807 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1808 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1808, 0, x_1779);
lean_ctor_set(x_1808, 1, x_1807);
x_1809 = lean_array_push(x_1806, x_1808);
x_1810 = lean_array_push(x_1809, x_1776);
x_1811 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1812, 0, x_1811);
lean_ctor_set(x_1812, 1, x_1810);
x_1813 = lean_array_push(x_1784, x_1812);
x_1814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1814, 0, x_1793);
lean_ctor_set(x_1814, 1, x_1813);
x_1815 = lean_array_push(x_1784, x_1814);
x_1816 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1817, 0, x_1816);
lean_ctor_set(x_1817, 1, x_1815);
x_1818 = lean_array_push(x_1799, x_1817);
x_1819 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1820, 0, x_1819);
lean_ctor_set(x_1820, 1, x_1818);
x_1821 = 1;
x_1822 = lean_box(x_1821);
if (lean_is_scalar(x_1777)) {
 x_1823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1823 = x_1777;
}
lean_ctor_set(x_1823, 0, x_1820);
lean_ctor_set(x_1823, 1, x_1822);
x_1824 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1824, 0, x_1775);
lean_ctor_set(x_1824, 1, x_1823);
if (lean_is_scalar(x_1781)) {
 x_1825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1825 = x_1781;
}
lean_ctor_set(x_1825, 0, x_1824);
lean_ctor_set(x_1825, 1, x_1780);
return x_1825;
}
}
}
else
{
lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; uint8_t x_1837; 
lean_dec(x_1135);
lean_inc(x_5);
x_1826 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_1827 = lean_ctor_get(x_1826, 0);
lean_inc(x_1827);
x_1828 = lean_ctor_get(x_1826, 1);
lean_inc(x_1828);
lean_dec(x_1826);
x_1829 = lean_nat_add(x_3, x_1134);
lean_dec(x_3);
x_1830 = l_Lean_mkHole(x_14);
lean_inc(x_1827);
x_1831 = l_Lean_Elab_Term_mkExplicitBinder(x_1827, x_1830);
x_1832 = lean_array_push(x_4, x_1831);
lean_inc(x_5);
x_1833 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1829, x_1832, x_5, x_1828);
x_1834 = lean_ctor_get(x_1833, 0);
lean_inc(x_1834);
x_1835 = lean_ctor_get(x_1834, 1);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1833, 1);
lean_inc(x_1836);
lean_dec(x_1833);
x_1837 = !lean_is_exclusive(x_1834);
if (x_1837 == 0)
{
lean_object* x_1838; uint8_t x_1839; 
x_1838 = lean_ctor_get(x_1834, 1);
lean_dec(x_1838);
x_1839 = !lean_is_exclusive(x_1835);
if (x_1839 == 0)
{
lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; uint8_t x_1843; 
x_1840 = lean_ctor_get(x_1835, 0);
x_1841 = lean_ctor_get(x_1835, 1);
lean_dec(x_1841);
x_1842 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1836);
lean_dec(x_5);
x_1843 = !lean_is_exclusive(x_1842);
if (x_1843 == 0)
{
lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; uint8_t x_1867; 
x_1844 = lean_ctor_get(x_1842, 0);
x_1845 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1844);
x_1846 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1846, 0, x_1844);
lean_ctor_set(x_1846, 1, x_1845);
x_1847 = l_Array_empty___closed__1;
x_1848 = lean_array_push(x_1847, x_1846);
x_1849 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1850 = lean_array_push(x_1848, x_1849);
x_1851 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1852 = lean_array_push(x_1851, x_1827);
x_1853 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1854, 0, x_1853);
lean_ctor_set(x_1854, 1, x_1852);
x_1855 = lean_array_push(x_1847, x_1854);
x_1856 = l_Lean_nullKind___closed__2;
x_1857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1857, 0, x_1856);
lean_ctor_set(x_1857, 1, x_1855);
x_1858 = lean_array_push(x_1850, x_1857);
x_1859 = lean_array_push(x_1858, x_1849);
x_1860 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1844);
x_1861 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1861, 0, x_1844);
lean_ctor_set(x_1861, 1, x_1860);
x_1862 = lean_array_push(x_1859, x_1861);
x_1863 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1844);
x_1864 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1864, 0, x_1844);
lean_ctor_set(x_1864, 1, x_1863);
x_1865 = lean_array_push(x_1847, x_1864);
lean_inc(x_14);
x_1866 = lean_array_push(x_1847, x_14);
x_1867 = !lean_is_exclusive(x_14);
if (x_1867 == 0)
{
lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; uint8_t x_1885; lean_object* x_1886; 
x_1868 = lean_ctor_get(x_14, 1);
lean_dec(x_1868);
x_1869 = lean_ctor_get(x_14, 0);
lean_dec(x_1869);
lean_ctor_set(x_14, 1, x_1866);
lean_ctor_set(x_14, 0, x_1856);
x_1870 = lean_array_push(x_1865, x_14);
x_1871 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1872 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1872, 0, x_1844);
lean_ctor_set(x_1872, 1, x_1871);
x_1873 = lean_array_push(x_1870, x_1872);
x_1874 = lean_array_push(x_1873, x_1840);
x_1875 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1876, 0, x_1875);
lean_ctor_set(x_1876, 1, x_1874);
x_1877 = lean_array_push(x_1847, x_1876);
x_1878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1878, 0, x_1856);
lean_ctor_set(x_1878, 1, x_1877);
x_1879 = lean_array_push(x_1847, x_1878);
x_1880 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1881, 0, x_1880);
lean_ctor_set(x_1881, 1, x_1879);
x_1882 = lean_array_push(x_1862, x_1881);
x_1883 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1884, 0, x_1883);
lean_ctor_set(x_1884, 1, x_1882);
x_1885 = 1;
x_1886 = lean_box(x_1885);
lean_ctor_set(x_1835, 1, x_1886);
lean_ctor_set(x_1835, 0, x_1884);
lean_ctor_set(x_1842, 0, x_1834);
return x_1842;
}
else
{
lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; uint8_t x_1903; lean_object* x_1904; 
lean_dec(x_14);
x_1887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1887, 0, x_1856);
lean_ctor_set(x_1887, 1, x_1866);
x_1888 = lean_array_push(x_1865, x_1887);
x_1889 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1890 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1890, 0, x_1844);
lean_ctor_set(x_1890, 1, x_1889);
x_1891 = lean_array_push(x_1888, x_1890);
x_1892 = lean_array_push(x_1891, x_1840);
x_1893 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1894, 0, x_1893);
lean_ctor_set(x_1894, 1, x_1892);
x_1895 = lean_array_push(x_1847, x_1894);
x_1896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1896, 0, x_1856);
lean_ctor_set(x_1896, 1, x_1895);
x_1897 = lean_array_push(x_1847, x_1896);
x_1898 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1899, 0, x_1898);
lean_ctor_set(x_1899, 1, x_1897);
x_1900 = lean_array_push(x_1862, x_1899);
x_1901 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1902, 0, x_1901);
lean_ctor_set(x_1902, 1, x_1900);
x_1903 = 1;
x_1904 = lean_box(x_1903);
lean_ctor_set(x_1835, 1, x_1904);
lean_ctor_set(x_1835, 0, x_1902);
lean_ctor_set(x_1842, 0, x_1834);
return x_1842;
}
}
else
{
lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; uint8_t x_1946; lean_object* x_1947; lean_object* x_1948; 
x_1905 = lean_ctor_get(x_1842, 0);
x_1906 = lean_ctor_get(x_1842, 1);
lean_inc(x_1906);
lean_inc(x_1905);
lean_dec(x_1842);
x_1907 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1905);
x_1908 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1908, 0, x_1905);
lean_ctor_set(x_1908, 1, x_1907);
x_1909 = l_Array_empty___closed__1;
x_1910 = lean_array_push(x_1909, x_1908);
x_1911 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1912 = lean_array_push(x_1910, x_1911);
x_1913 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1914 = lean_array_push(x_1913, x_1827);
x_1915 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1916, 0, x_1915);
lean_ctor_set(x_1916, 1, x_1914);
x_1917 = lean_array_push(x_1909, x_1916);
x_1918 = l_Lean_nullKind___closed__2;
x_1919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1919, 0, x_1918);
lean_ctor_set(x_1919, 1, x_1917);
x_1920 = lean_array_push(x_1912, x_1919);
x_1921 = lean_array_push(x_1920, x_1911);
x_1922 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1905);
x_1923 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1923, 0, x_1905);
lean_ctor_set(x_1923, 1, x_1922);
x_1924 = lean_array_push(x_1921, x_1923);
x_1925 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1905);
x_1926 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1926, 0, x_1905);
lean_ctor_set(x_1926, 1, x_1925);
x_1927 = lean_array_push(x_1909, x_1926);
lean_inc(x_14);
x_1928 = lean_array_push(x_1909, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1929 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1929 = lean_box(0);
}
if (lean_is_scalar(x_1929)) {
 x_1930 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1930 = x_1929;
}
lean_ctor_set(x_1930, 0, x_1918);
lean_ctor_set(x_1930, 1, x_1928);
x_1931 = lean_array_push(x_1927, x_1930);
x_1932 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1933 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1933, 0, x_1905);
lean_ctor_set(x_1933, 1, x_1932);
x_1934 = lean_array_push(x_1931, x_1933);
x_1935 = lean_array_push(x_1934, x_1840);
x_1936 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1937, 0, x_1936);
lean_ctor_set(x_1937, 1, x_1935);
x_1938 = lean_array_push(x_1909, x_1937);
x_1939 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1939, 0, x_1918);
lean_ctor_set(x_1939, 1, x_1938);
x_1940 = lean_array_push(x_1909, x_1939);
x_1941 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1942 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1942, 0, x_1941);
lean_ctor_set(x_1942, 1, x_1940);
x_1943 = lean_array_push(x_1924, x_1942);
x_1944 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1945 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1945, 0, x_1944);
lean_ctor_set(x_1945, 1, x_1943);
x_1946 = 1;
x_1947 = lean_box(x_1946);
lean_ctor_set(x_1835, 1, x_1947);
lean_ctor_set(x_1835, 0, x_1945);
x_1948 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1948, 0, x_1834);
lean_ctor_set(x_1948, 1, x_1906);
return x_1948;
}
}
else
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; uint8_t x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; 
x_1949 = lean_ctor_get(x_1835, 0);
lean_inc(x_1949);
lean_dec(x_1835);
x_1950 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1836);
lean_dec(x_5);
x_1951 = lean_ctor_get(x_1950, 0);
lean_inc(x_1951);
x_1952 = lean_ctor_get(x_1950, 1);
lean_inc(x_1952);
if (lean_is_exclusive(x_1950)) {
 lean_ctor_release(x_1950, 0);
 lean_ctor_release(x_1950, 1);
 x_1953 = x_1950;
} else {
 lean_dec_ref(x_1950);
 x_1953 = lean_box(0);
}
x_1954 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_1951);
x_1955 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1955, 0, x_1951);
lean_ctor_set(x_1955, 1, x_1954);
x_1956 = l_Array_empty___closed__1;
x_1957 = lean_array_push(x_1956, x_1955);
x_1958 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_1959 = lean_array_push(x_1957, x_1958);
x_1960 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_1961 = lean_array_push(x_1960, x_1827);
x_1962 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_1963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1963, 0, x_1962);
lean_ctor_set(x_1963, 1, x_1961);
x_1964 = lean_array_push(x_1956, x_1963);
x_1965 = l_Lean_nullKind___closed__2;
x_1966 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1966, 0, x_1965);
lean_ctor_set(x_1966, 1, x_1964);
x_1967 = lean_array_push(x_1959, x_1966);
x_1968 = lean_array_push(x_1967, x_1958);
x_1969 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_1951);
x_1970 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1970, 0, x_1951);
lean_ctor_set(x_1970, 1, x_1969);
x_1971 = lean_array_push(x_1968, x_1970);
x_1972 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_1951);
x_1973 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1973, 0, x_1951);
lean_ctor_set(x_1973, 1, x_1972);
x_1974 = lean_array_push(x_1956, x_1973);
lean_inc(x_14);
x_1975 = lean_array_push(x_1956, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_1976 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1976 = lean_box(0);
}
if (lean_is_scalar(x_1976)) {
 x_1977 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1977 = x_1976;
}
lean_ctor_set(x_1977, 0, x_1965);
lean_ctor_set(x_1977, 1, x_1975);
x_1978 = lean_array_push(x_1974, x_1977);
x_1979 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_1980 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1980, 0, x_1951);
lean_ctor_set(x_1980, 1, x_1979);
x_1981 = lean_array_push(x_1978, x_1980);
x_1982 = lean_array_push(x_1981, x_1949);
x_1983 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_1984 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1984, 0, x_1983);
lean_ctor_set(x_1984, 1, x_1982);
x_1985 = lean_array_push(x_1956, x_1984);
x_1986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1986, 0, x_1965);
lean_ctor_set(x_1986, 1, x_1985);
x_1987 = lean_array_push(x_1956, x_1986);
x_1988 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_1989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1989, 0, x_1988);
lean_ctor_set(x_1989, 1, x_1987);
x_1990 = lean_array_push(x_1971, x_1989);
x_1991 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_1992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1992, 0, x_1991);
lean_ctor_set(x_1992, 1, x_1990);
x_1993 = 1;
x_1994 = lean_box(x_1993);
x_1995 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1995, 0, x_1992);
lean_ctor_set(x_1995, 1, x_1994);
lean_ctor_set(x_1834, 1, x_1995);
if (lean_is_scalar(x_1953)) {
 x_1996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1996 = x_1953;
}
lean_ctor_set(x_1996, 0, x_1834);
lean_ctor_set(x_1996, 1, x_1952);
return x_1996;
}
}
else
{
lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; uint8_t x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; 
x_1997 = lean_ctor_get(x_1834, 0);
lean_inc(x_1997);
lean_dec(x_1834);
x_1998 = lean_ctor_get(x_1835, 0);
lean_inc(x_1998);
if (lean_is_exclusive(x_1835)) {
 lean_ctor_release(x_1835, 0);
 lean_ctor_release(x_1835, 1);
 x_1999 = x_1835;
} else {
 lean_dec_ref(x_1835);
 x_1999 = lean_box(0);
}
x_2000 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_1836);
lean_dec(x_5);
x_2001 = lean_ctor_get(x_2000, 0);
lean_inc(x_2001);
x_2002 = lean_ctor_get(x_2000, 1);
lean_inc(x_2002);
if (lean_is_exclusive(x_2000)) {
 lean_ctor_release(x_2000, 0);
 lean_ctor_release(x_2000, 1);
 x_2003 = x_2000;
} else {
 lean_dec_ref(x_2000);
 x_2003 = lean_box(0);
}
x_2004 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2001);
x_2005 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2005, 0, x_2001);
lean_ctor_set(x_2005, 1, x_2004);
x_2006 = l_Array_empty___closed__1;
x_2007 = lean_array_push(x_2006, x_2005);
x_2008 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2009 = lean_array_push(x_2007, x_2008);
x_2010 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2011 = lean_array_push(x_2010, x_1827);
x_2012 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2013, 0, x_2012);
lean_ctor_set(x_2013, 1, x_2011);
x_2014 = lean_array_push(x_2006, x_2013);
x_2015 = l_Lean_nullKind___closed__2;
x_2016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2016, 0, x_2015);
lean_ctor_set(x_2016, 1, x_2014);
x_2017 = lean_array_push(x_2009, x_2016);
x_2018 = lean_array_push(x_2017, x_2008);
x_2019 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2001);
x_2020 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2020, 0, x_2001);
lean_ctor_set(x_2020, 1, x_2019);
x_2021 = lean_array_push(x_2018, x_2020);
x_2022 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2001);
x_2023 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2023, 0, x_2001);
lean_ctor_set(x_2023, 1, x_2022);
x_2024 = lean_array_push(x_2006, x_2023);
lean_inc(x_14);
x_2025 = lean_array_push(x_2006, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2026 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2026 = lean_box(0);
}
if (lean_is_scalar(x_2026)) {
 x_2027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2027 = x_2026;
}
lean_ctor_set(x_2027, 0, x_2015);
lean_ctor_set(x_2027, 1, x_2025);
x_2028 = lean_array_push(x_2024, x_2027);
x_2029 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2030 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2030, 0, x_2001);
lean_ctor_set(x_2030, 1, x_2029);
x_2031 = lean_array_push(x_2028, x_2030);
x_2032 = lean_array_push(x_2031, x_1998);
x_2033 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2034 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2034, 0, x_2033);
lean_ctor_set(x_2034, 1, x_2032);
x_2035 = lean_array_push(x_2006, x_2034);
x_2036 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2036, 0, x_2015);
lean_ctor_set(x_2036, 1, x_2035);
x_2037 = lean_array_push(x_2006, x_2036);
x_2038 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2039 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2039, 0, x_2038);
lean_ctor_set(x_2039, 1, x_2037);
x_2040 = lean_array_push(x_2021, x_2039);
x_2041 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2042, 0, x_2041);
lean_ctor_set(x_2042, 1, x_2040);
x_2043 = 1;
x_2044 = lean_box(x_2043);
if (lean_is_scalar(x_1999)) {
 x_2045 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2045 = x_1999;
}
lean_ctor_set(x_2045, 0, x_2042);
lean_ctor_set(x_2045, 1, x_2044);
x_2046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2046, 0, x_1997);
lean_ctor_set(x_2046, 1, x_2045);
if (lean_is_scalar(x_2003)) {
 x_2047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2047 = x_2003;
}
lean_ctor_set(x_2047, 0, x_2046);
lean_ctor_set(x_2047, 1, x_2002);
return x_2047;
}
}
}
}
else
{
lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; 
lean_dec(x_220);
lean_inc(x_5);
x_2048 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2049 = lean_ctor_get(x_2048, 0);
lean_inc(x_2049);
x_2050 = lean_ctor_get(x_2048, 1);
lean_inc(x_2050);
lean_dec(x_2048);
x_2051 = lean_unsigned_to_nat(1u);
x_2052 = lean_nat_add(x_3, x_2051);
lean_dec(x_3);
x_2053 = l_Lean_Elab_Term_mkExplicitBinder(x_2049, x_14);
x_2054 = lean_array_push(x_4, x_2053);
x_3 = x_2052;
x_4 = x_2054;
x_6 = x_2050;
goto _start;
}
}
else
{
lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; 
lean_dec(x_220);
x_2056 = lean_unsigned_to_nat(1u);
x_2057 = lean_nat_add(x_3, x_2056);
lean_dec(x_3);
x_2058 = lean_array_push(x_4, x_14);
x_3 = x_2057;
x_4 = x_2058;
goto _start;
}
}
else
{
lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
lean_dec(x_220);
x_2060 = lean_unsigned_to_nat(1u);
x_2061 = lean_nat_add(x_3, x_2060);
lean_dec(x_3);
x_2062 = lean_array_push(x_4, x_14);
x_3 = x_2061;
x_4 = x_2062;
goto _start;
}
}
else
{
lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; 
lean_dec(x_220);
x_2064 = lean_unsigned_to_nat(1u);
x_2065 = lean_nat_add(x_3, x_2064);
lean_dec(x_3);
x_2066 = lean_array_push(x_4, x_14);
x_3 = x_2065;
x_4 = x_2066;
goto _start;
}
}
else
{
lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; 
lean_dec(x_220);
x_2068 = lean_unsigned_to_nat(1u);
x_2069 = lean_nat_add(x_3, x_2068);
lean_dec(x_3);
x_2070 = lean_array_push(x_4, x_14);
x_3 = x_2069;
x_4 = x_2070;
goto _start;
}
}
}
}
}
else
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; uint8_t x_2084; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_inc(x_5);
x_2072 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2073 = lean_ctor_get(x_2072, 0);
lean_inc(x_2073);
x_2074 = lean_ctor_get(x_2072, 1);
lean_inc(x_2074);
lean_dec(x_2072);
x_2075 = lean_unsigned_to_nat(1u);
x_2076 = lean_nat_add(x_3, x_2075);
lean_dec(x_3);
x_2077 = l_Lean_mkHole(x_14);
lean_inc(x_2073);
x_2078 = l_Lean_Elab_Term_mkExplicitBinder(x_2073, x_2077);
x_2079 = lean_array_push(x_4, x_2078);
lean_inc(x_5);
x_2080 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2076, x_2079, x_5, x_2074);
x_2081 = lean_ctor_get(x_2080, 0);
lean_inc(x_2081);
x_2082 = lean_ctor_get(x_2081, 1);
lean_inc(x_2082);
x_2083 = lean_ctor_get(x_2080, 1);
lean_inc(x_2083);
lean_dec(x_2080);
x_2084 = !lean_is_exclusive(x_2081);
if (x_2084 == 0)
{
lean_object* x_2085; uint8_t x_2086; 
x_2085 = lean_ctor_get(x_2081, 1);
lean_dec(x_2085);
x_2086 = !lean_is_exclusive(x_2082);
if (x_2086 == 0)
{
lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; uint8_t x_2090; 
x_2087 = lean_ctor_get(x_2082, 0);
x_2088 = lean_ctor_get(x_2082, 1);
lean_dec(x_2088);
x_2089 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2083);
lean_dec(x_5);
x_2090 = !lean_is_exclusive(x_2089);
if (x_2090 == 0)
{
lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; uint8_t x_2114; 
x_2091 = lean_ctor_get(x_2089, 0);
x_2092 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2091);
x_2093 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2093, 0, x_2091);
lean_ctor_set(x_2093, 1, x_2092);
x_2094 = l_Array_empty___closed__1;
x_2095 = lean_array_push(x_2094, x_2093);
x_2096 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2097 = lean_array_push(x_2095, x_2096);
x_2098 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2099 = lean_array_push(x_2098, x_2073);
x_2100 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2101, 0, x_2100);
lean_ctor_set(x_2101, 1, x_2099);
x_2102 = lean_array_push(x_2094, x_2101);
x_2103 = l_Lean_nullKind___closed__2;
x_2104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2104, 0, x_2103);
lean_ctor_set(x_2104, 1, x_2102);
x_2105 = lean_array_push(x_2097, x_2104);
x_2106 = lean_array_push(x_2105, x_2096);
x_2107 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2091);
x_2108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2108, 0, x_2091);
lean_ctor_set(x_2108, 1, x_2107);
x_2109 = lean_array_push(x_2106, x_2108);
x_2110 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2091);
x_2111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2111, 0, x_2091);
lean_ctor_set(x_2111, 1, x_2110);
x_2112 = lean_array_push(x_2094, x_2111);
lean_inc(x_14);
x_2113 = lean_array_push(x_2094, x_14);
x_2114 = !lean_is_exclusive(x_14);
if (x_2114 == 0)
{
lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; uint8_t x_2132; lean_object* x_2133; 
x_2115 = lean_ctor_get(x_14, 1);
lean_dec(x_2115);
x_2116 = lean_ctor_get(x_14, 0);
lean_dec(x_2116);
lean_ctor_set(x_14, 1, x_2113);
lean_ctor_set(x_14, 0, x_2103);
x_2117 = lean_array_push(x_2112, x_14);
x_2118 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2119, 0, x_2091);
lean_ctor_set(x_2119, 1, x_2118);
x_2120 = lean_array_push(x_2117, x_2119);
x_2121 = lean_array_push(x_2120, x_2087);
x_2122 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2123, 0, x_2122);
lean_ctor_set(x_2123, 1, x_2121);
x_2124 = lean_array_push(x_2094, x_2123);
x_2125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2125, 0, x_2103);
lean_ctor_set(x_2125, 1, x_2124);
x_2126 = lean_array_push(x_2094, x_2125);
x_2127 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2128, 0, x_2127);
lean_ctor_set(x_2128, 1, x_2126);
x_2129 = lean_array_push(x_2109, x_2128);
x_2130 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2131, 0, x_2130);
lean_ctor_set(x_2131, 1, x_2129);
x_2132 = 1;
x_2133 = lean_box(x_2132);
lean_ctor_set(x_2082, 1, x_2133);
lean_ctor_set(x_2082, 0, x_2131);
lean_ctor_set(x_2089, 0, x_2081);
return x_2089;
}
else
{
lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; uint8_t x_2150; lean_object* x_2151; 
lean_dec(x_14);
x_2134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2134, 0, x_2103);
lean_ctor_set(x_2134, 1, x_2113);
x_2135 = lean_array_push(x_2112, x_2134);
x_2136 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2137, 0, x_2091);
lean_ctor_set(x_2137, 1, x_2136);
x_2138 = lean_array_push(x_2135, x_2137);
x_2139 = lean_array_push(x_2138, x_2087);
x_2140 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2141, 0, x_2140);
lean_ctor_set(x_2141, 1, x_2139);
x_2142 = lean_array_push(x_2094, x_2141);
x_2143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2143, 0, x_2103);
lean_ctor_set(x_2143, 1, x_2142);
x_2144 = lean_array_push(x_2094, x_2143);
x_2145 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2146, 0, x_2145);
lean_ctor_set(x_2146, 1, x_2144);
x_2147 = lean_array_push(x_2109, x_2146);
x_2148 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2149, 0, x_2148);
lean_ctor_set(x_2149, 1, x_2147);
x_2150 = 1;
x_2151 = lean_box(x_2150);
lean_ctor_set(x_2082, 1, x_2151);
lean_ctor_set(x_2082, 0, x_2149);
lean_ctor_set(x_2089, 0, x_2081);
return x_2089;
}
}
else
{
lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; uint8_t x_2193; lean_object* x_2194; lean_object* x_2195; 
x_2152 = lean_ctor_get(x_2089, 0);
x_2153 = lean_ctor_get(x_2089, 1);
lean_inc(x_2153);
lean_inc(x_2152);
lean_dec(x_2089);
x_2154 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2152);
x_2155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2155, 0, x_2152);
lean_ctor_set(x_2155, 1, x_2154);
x_2156 = l_Array_empty___closed__1;
x_2157 = lean_array_push(x_2156, x_2155);
x_2158 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2159 = lean_array_push(x_2157, x_2158);
x_2160 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2161 = lean_array_push(x_2160, x_2073);
x_2162 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2163, 0, x_2162);
lean_ctor_set(x_2163, 1, x_2161);
x_2164 = lean_array_push(x_2156, x_2163);
x_2165 = l_Lean_nullKind___closed__2;
x_2166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2166, 0, x_2165);
lean_ctor_set(x_2166, 1, x_2164);
x_2167 = lean_array_push(x_2159, x_2166);
x_2168 = lean_array_push(x_2167, x_2158);
x_2169 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2152);
x_2170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2170, 0, x_2152);
lean_ctor_set(x_2170, 1, x_2169);
x_2171 = lean_array_push(x_2168, x_2170);
x_2172 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2152);
x_2173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2173, 0, x_2152);
lean_ctor_set(x_2173, 1, x_2172);
x_2174 = lean_array_push(x_2156, x_2173);
lean_inc(x_14);
x_2175 = lean_array_push(x_2156, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2176 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2176 = lean_box(0);
}
if (lean_is_scalar(x_2176)) {
 x_2177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2177 = x_2176;
}
lean_ctor_set(x_2177, 0, x_2165);
lean_ctor_set(x_2177, 1, x_2175);
x_2178 = lean_array_push(x_2174, x_2177);
x_2179 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2180, 0, x_2152);
lean_ctor_set(x_2180, 1, x_2179);
x_2181 = lean_array_push(x_2178, x_2180);
x_2182 = lean_array_push(x_2181, x_2087);
x_2183 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2184, 0, x_2183);
lean_ctor_set(x_2184, 1, x_2182);
x_2185 = lean_array_push(x_2156, x_2184);
x_2186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2186, 0, x_2165);
lean_ctor_set(x_2186, 1, x_2185);
x_2187 = lean_array_push(x_2156, x_2186);
x_2188 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2189, 0, x_2188);
lean_ctor_set(x_2189, 1, x_2187);
x_2190 = lean_array_push(x_2171, x_2189);
x_2191 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2192, 0, x_2191);
lean_ctor_set(x_2192, 1, x_2190);
x_2193 = 1;
x_2194 = lean_box(x_2193);
lean_ctor_set(x_2082, 1, x_2194);
lean_ctor_set(x_2082, 0, x_2192);
x_2195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2195, 0, x_2081);
lean_ctor_set(x_2195, 1, x_2153);
return x_2195;
}
}
else
{
lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; uint8_t x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; 
x_2196 = lean_ctor_get(x_2082, 0);
lean_inc(x_2196);
lean_dec(x_2082);
x_2197 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2083);
lean_dec(x_5);
x_2198 = lean_ctor_get(x_2197, 0);
lean_inc(x_2198);
x_2199 = lean_ctor_get(x_2197, 1);
lean_inc(x_2199);
if (lean_is_exclusive(x_2197)) {
 lean_ctor_release(x_2197, 0);
 lean_ctor_release(x_2197, 1);
 x_2200 = x_2197;
} else {
 lean_dec_ref(x_2197);
 x_2200 = lean_box(0);
}
x_2201 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2198);
x_2202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2202, 0, x_2198);
lean_ctor_set(x_2202, 1, x_2201);
x_2203 = l_Array_empty___closed__1;
x_2204 = lean_array_push(x_2203, x_2202);
x_2205 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2206 = lean_array_push(x_2204, x_2205);
x_2207 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2208 = lean_array_push(x_2207, x_2073);
x_2209 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2210, 0, x_2209);
lean_ctor_set(x_2210, 1, x_2208);
x_2211 = lean_array_push(x_2203, x_2210);
x_2212 = l_Lean_nullKind___closed__2;
x_2213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2213, 0, x_2212);
lean_ctor_set(x_2213, 1, x_2211);
x_2214 = lean_array_push(x_2206, x_2213);
x_2215 = lean_array_push(x_2214, x_2205);
x_2216 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2198);
x_2217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2217, 0, x_2198);
lean_ctor_set(x_2217, 1, x_2216);
x_2218 = lean_array_push(x_2215, x_2217);
x_2219 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2198);
x_2220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2220, 0, x_2198);
lean_ctor_set(x_2220, 1, x_2219);
x_2221 = lean_array_push(x_2203, x_2220);
lean_inc(x_14);
x_2222 = lean_array_push(x_2203, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2223 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2223 = lean_box(0);
}
if (lean_is_scalar(x_2223)) {
 x_2224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2224 = x_2223;
}
lean_ctor_set(x_2224, 0, x_2212);
lean_ctor_set(x_2224, 1, x_2222);
x_2225 = lean_array_push(x_2221, x_2224);
x_2226 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2227, 0, x_2198);
lean_ctor_set(x_2227, 1, x_2226);
x_2228 = lean_array_push(x_2225, x_2227);
x_2229 = lean_array_push(x_2228, x_2196);
x_2230 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2231, 0, x_2230);
lean_ctor_set(x_2231, 1, x_2229);
x_2232 = lean_array_push(x_2203, x_2231);
x_2233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2233, 0, x_2212);
lean_ctor_set(x_2233, 1, x_2232);
x_2234 = lean_array_push(x_2203, x_2233);
x_2235 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2236, 0, x_2235);
lean_ctor_set(x_2236, 1, x_2234);
x_2237 = lean_array_push(x_2218, x_2236);
x_2238 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2239, 0, x_2238);
lean_ctor_set(x_2239, 1, x_2237);
x_2240 = 1;
x_2241 = lean_box(x_2240);
x_2242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2242, 0, x_2239);
lean_ctor_set(x_2242, 1, x_2241);
lean_ctor_set(x_2081, 1, x_2242);
if (lean_is_scalar(x_2200)) {
 x_2243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2243 = x_2200;
}
lean_ctor_set(x_2243, 0, x_2081);
lean_ctor_set(x_2243, 1, x_2199);
return x_2243;
}
}
else
{
lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; uint8_t x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; 
x_2244 = lean_ctor_get(x_2081, 0);
lean_inc(x_2244);
lean_dec(x_2081);
x_2245 = lean_ctor_get(x_2082, 0);
lean_inc(x_2245);
if (lean_is_exclusive(x_2082)) {
 lean_ctor_release(x_2082, 0);
 lean_ctor_release(x_2082, 1);
 x_2246 = x_2082;
} else {
 lean_dec_ref(x_2082);
 x_2246 = lean_box(0);
}
x_2247 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2083);
lean_dec(x_5);
x_2248 = lean_ctor_get(x_2247, 0);
lean_inc(x_2248);
x_2249 = lean_ctor_get(x_2247, 1);
lean_inc(x_2249);
if (lean_is_exclusive(x_2247)) {
 lean_ctor_release(x_2247, 0);
 lean_ctor_release(x_2247, 1);
 x_2250 = x_2247;
} else {
 lean_dec_ref(x_2247);
 x_2250 = lean_box(0);
}
x_2251 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2248);
x_2252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2252, 0, x_2248);
lean_ctor_set(x_2252, 1, x_2251);
x_2253 = l_Array_empty___closed__1;
x_2254 = lean_array_push(x_2253, x_2252);
x_2255 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2256 = lean_array_push(x_2254, x_2255);
x_2257 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2258 = lean_array_push(x_2257, x_2073);
x_2259 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2260, 0, x_2259);
lean_ctor_set(x_2260, 1, x_2258);
x_2261 = lean_array_push(x_2253, x_2260);
x_2262 = l_Lean_nullKind___closed__2;
x_2263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2263, 0, x_2262);
lean_ctor_set(x_2263, 1, x_2261);
x_2264 = lean_array_push(x_2256, x_2263);
x_2265 = lean_array_push(x_2264, x_2255);
x_2266 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2248);
x_2267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2267, 0, x_2248);
lean_ctor_set(x_2267, 1, x_2266);
x_2268 = lean_array_push(x_2265, x_2267);
x_2269 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2248);
x_2270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2270, 0, x_2248);
lean_ctor_set(x_2270, 1, x_2269);
x_2271 = lean_array_push(x_2253, x_2270);
lean_inc(x_14);
x_2272 = lean_array_push(x_2253, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2273 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2273 = lean_box(0);
}
if (lean_is_scalar(x_2273)) {
 x_2274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2274 = x_2273;
}
lean_ctor_set(x_2274, 0, x_2262);
lean_ctor_set(x_2274, 1, x_2272);
x_2275 = lean_array_push(x_2271, x_2274);
x_2276 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2277 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2277, 0, x_2248);
lean_ctor_set(x_2277, 1, x_2276);
x_2278 = lean_array_push(x_2275, x_2277);
x_2279 = lean_array_push(x_2278, x_2245);
x_2280 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2281, 0, x_2280);
lean_ctor_set(x_2281, 1, x_2279);
x_2282 = lean_array_push(x_2253, x_2281);
x_2283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2283, 0, x_2262);
lean_ctor_set(x_2283, 1, x_2282);
x_2284 = lean_array_push(x_2253, x_2283);
x_2285 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2286, 0, x_2285);
lean_ctor_set(x_2286, 1, x_2284);
x_2287 = lean_array_push(x_2268, x_2286);
x_2288 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2289, 0, x_2288);
lean_ctor_set(x_2289, 1, x_2287);
x_2290 = 1;
x_2291 = lean_box(x_2290);
if (lean_is_scalar(x_2246)) {
 x_2292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2292 = x_2246;
}
lean_ctor_set(x_2292, 0, x_2289);
lean_ctor_set(x_2292, 1, x_2291);
x_2293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2293, 0, x_2244);
lean_ctor_set(x_2293, 1, x_2292);
if (lean_is_scalar(x_2250)) {
 x_2294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2294 = x_2250;
}
lean_ctor_set(x_2294, 0, x_2293);
lean_ctor_set(x_2294, 1, x_2249);
return x_2294;
}
}
}
else
{
lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; uint8_t x_2307; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_inc(x_5);
x_2295 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2296 = lean_ctor_get(x_2295, 0);
lean_inc(x_2296);
x_2297 = lean_ctor_get(x_2295, 1);
lean_inc(x_2297);
lean_dec(x_2295);
x_2298 = lean_unsigned_to_nat(1u);
x_2299 = lean_nat_add(x_3, x_2298);
lean_dec(x_3);
x_2300 = l_Lean_mkHole(x_14);
lean_inc(x_2296);
x_2301 = l_Lean_Elab_Term_mkExplicitBinder(x_2296, x_2300);
x_2302 = lean_array_push(x_4, x_2301);
lean_inc(x_5);
x_2303 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2299, x_2302, x_5, x_2297);
x_2304 = lean_ctor_get(x_2303, 0);
lean_inc(x_2304);
x_2305 = lean_ctor_get(x_2304, 1);
lean_inc(x_2305);
x_2306 = lean_ctor_get(x_2303, 1);
lean_inc(x_2306);
lean_dec(x_2303);
x_2307 = !lean_is_exclusive(x_2304);
if (x_2307 == 0)
{
lean_object* x_2308; uint8_t x_2309; 
x_2308 = lean_ctor_get(x_2304, 1);
lean_dec(x_2308);
x_2309 = !lean_is_exclusive(x_2305);
if (x_2309 == 0)
{
lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; uint8_t x_2313; 
x_2310 = lean_ctor_get(x_2305, 0);
x_2311 = lean_ctor_get(x_2305, 1);
lean_dec(x_2311);
x_2312 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2306);
lean_dec(x_5);
x_2313 = !lean_is_exclusive(x_2312);
if (x_2313 == 0)
{
lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; uint8_t x_2337; 
x_2314 = lean_ctor_get(x_2312, 0);
x_2315 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2314);
x_2316 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2316, 0, x_2314);
lean_ctor_set(x_2316, 1, x_2315);
x_2317 = l_Array_empty___closed__1;
x_2318 = lean_array_push(x_2317, x_2316);
x_2319 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2320 = lean_array_push(x_2318, x_2319);
x_2321 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2322 = lean_array_push(x_2321, x_2296);
x_2323 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2324, 0, x_2323);
lean_ctor_set(x_2324, 1, x_2322);
x_2325 = lean_array_push(x_2317, x_2324);
x_2326 = l_Lean_nullKind___closed__2;
x_2327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2327, 0, x_2326);
lean_ctor_set(x_2327, 1, x_2325);
x_2328 = lean_array_push(x_2320, x_2327);
x_2329 = lean_array_push(x_2328, x_2319);
x_2330 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2314);
x_2331 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2331, 0, x_2314);
lean_ctor_set(x_2331, 1, x_2330);
x_2332 = lean_array_push(x_2329, x_2331);
x_2333 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2314);
x_2334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2334, 0, x_2314);
lean_ctor_set(x_2334, 1, x_2333);
x_2335 = lean_array_push(x_2317, x_2334);
lean_inc(x_14);
x_2336 = lean_array_push(x_2317, x_14);
x_2337 = !lean_is_exclusive(x_14);
if (x_2337 == 0)
{
lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; uint8_t x_2355; lean_object* x_2356; 
x_2338 = lean_ctor_get(x_14, 1);
lean_dec(x_2338);
x_2339 = lean_ctor_get(x_14, 0);
lean_dec(x_2339);
lean_ctor_set(x_14, 1, x_2336);
lean_ctor_set(x_14, 0, x_2326);
x_2340 = lean_array_push(x_2335, x_14);
x_2341 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2342, 0, x_2314);
lean_ctor_set(x_2342, 1, x_2341);
x_2343 = lean_array_push(x_2340, x_2342);
x_2344 = lean_array_push(x_2343, x_2310);
x_2345 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2346, 0, x_2345);
lean_ctor_set(x_2346, 1, x_2344);
x_2347 = lean_array_push(x_2317, x_2346);
x_2348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2348, 0, x_2326);
lean_ctor_set(x_2348, 1, x_2347);
x_2349 = lean_array_push(x_2317, x_2348);
x_2350 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2351, 0, x_2350);
lean_ctor_set(x_2351, 1, x_2349);
x_2352 = lean_array_push(x_2332, x_2351);
x_2353 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2354, 0, x_2353);
lean_ctor_set(x_2354, 1, x_2352);
x_2355 = 1;
x_2356 = lean_box(x_2355);
lean_ctor_set(x_2305, 1, x_2356);
lean_ctor_set(x_2305, 0, x_2354);
lean_ctor_set(x_2312, 0, x_2304);
return x_2312;
}
else
{
lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; uint8_t x_2373; lean_object* x_2374; 
lean_dec(x_14);
x_2357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2357, 0, x_2326);
lean_ctor_set(x_2357, 1, x_2336);
x_2358 = lean_array_push(x_2335, x_2357);
x_2359 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2360, 0, x_2314);
lean_ctor_set(x_2360, 1, x_2359);
x_2361 = lean_array_push(x_2358, x_2360);
x_2362 = lean_array_push(x_2361, x_2310);
x_2363 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2364, 0, x_2363);
lean_ctor_set(x_2364, 1, x_2362);
x_2365 = lean_array_push(x_2317, x_2364);
x_2366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2366, 0, x_2326);
lean_ctor_set(x_2366, 1, x_2365);
x_2367 = lean_array_push(x_2317, x_2366);
x_2368 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2369, 0, x_2368);
lean_ctor_set(x_2369, 1, x_2367);
x_2370 = lean_array_push(x_2332, x_2369);
x_2371 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2372, 0, x_2371);
lean_ctor_set(x_2372, 1, x_2370);
x_2373 = 1;
x_2374 = lean_box(x_2373);
lean_ctor_set(x_2305, 1, x_2374);
lean_ctor_set(x_2305, 0, x_2372);
lean_ctor_set(x_2312, 0, x_2304);
return x_2312;
}
}
else
{
lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; uint8_t x_2416; lean_object* x_2417; lean_object* x_2418; 
x_2375 = lean_ctor_get(x_2312, 0);
x_2376 = lean_ctor_get(x_2312, 1);
lean_inc(x_2376);
lean_inc(x_2375);
lean_dec(x_2312);
x_2377 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2375);
x_2378 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2378, 0, x_2375);
lean_ctor_set(x_2378, 1, x_2377);
x_2379 = l_Array_empty___closed__1;
x_2380 = lean_array_push(x_2379, x_2378);
x_2381 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2382 = lean_array_push(x_2380, x_2381);
x_2383 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2384 = lean_array_push(x_2383, x_2296);
x_2385 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2386, 0, x_2385);
lean_ctor_set(x_2386, 1, x_2384);
x_2387 = lean_array_push(x_2379, x_2386);
x_2388 = l_Lean_nullKind___closed__2;
x_2389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2389, 0, x_2388);
lean_ctor_set(x_2389, 1, x_2387);
x_2390 = lean_array_push(x_2382, x_2389);
x_2391 = lean_array_push(x_2390, x_2381);
x_2392 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2375);
x_2393 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2393, 0, x_2375);
lean_ctor_set(x_2393, 1, x_2392);
x_2394 = lean_array_push(x_2391, x_2393);
x_2395 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2375);
x_2396 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2396, 0, x_2375);
lean_ctor_set(x_2396, 1, x_2395);
x_2397 = lean_array_push(x_2379, x_2396);
lean_inc(x_14);
x_2398 = lean_array_push(x_2379, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2399 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2399 = lean_box(0);
}
if (lean_is_scalar(x_2399)) {
 x_2400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2400 = x_2399;
}
lean_ctor_set(x_2400, 0, x_2388);
lean_ctor_set(x_2400, 1, x_2398);
x_2401 = lean_array_push(x_2397, x_2400);
x_2402 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2403, 0, x_2375);
lean_ctor_set(x_2403, 1, x_2402);
x_2404 = lean_array_push(x_2401, x_2403);
x_2405 = lean_array_push(x_2404, x_2310);
x_2406 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2407, 0, x_2406);
lean_ctor_set(x_2407, 1, x_2405);
x_2408 = lean_array_push(x_2379, x_2407);
x_2409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2409, 0, x_2388);
lean_ctor_set(x_2409, 1, x_2408);
x_2410 = lean_array_push(x_2379, x_2409);
x_2411 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2412, 0, x_2411);
lean_ctor_set(x_2412, 1, x_2410);
x_2413 = lean_array_push(x_2394, x_2412);
x_2414 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2415, 0, x_2414);
lean_ctor_set(x_2415, 1, x_2413);
x_2416 = 1;
x_2417 = lean_box(x_2416);
lean_ctor_set(x_2305, 1, x_2417);
lean_ctor_set(x_2305, 0, x_2415);
x_2418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2418, 0, x_2304);
lean_ctor_set(x_2418, 1, x_2376);
return x_2418;
}
}
else
{
lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; uint8_t x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; 
x_2419 = lean_ctor_get(x_2305, 0);
lean_inc(x_2419);
lean_dec(x_2305);
x_2420 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2306);
lean_dec(x_5);
x_2421 = lean_ctor_get(x_2420, 0);
lean_inc(x_2421);
x_2422 = lean_ctor_get(x_2420, 1);
lean_inc(x_2422);
if (lean_is_exclusive(x_2420)) {
 lean_ctor_release(x_2420, 0);
 lean_ctor_release(x_2420, 1);
 x_2423 = x_2420;
} else {
 lean_dec_ref(x_2420);
 x_2423 = lean_box(0);
}
x_2424 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2421);
x_2425 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2425, 0, x_2421);
lean_ctor_set(x_2425, 1, x_2424);
x_2426 = l_Array_empty___closed__1;
x_2427 = lean_array_push(x_2426, x_2425);
x_2428 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2429 = lean_array_push(x_2427, x_2428);
x_2430 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2431 = lean_array_push(x_2430, x_2296);
x_2432 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2433, 0, x_2432);
lean_ctor_set(x_2433, 1, x_2431);
x_2434 = lean_array_push(x_2426, x_2433);
x_2435 = l_Lean_nullKind___closed__2;
x_2436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2436, 0, x_2435);
lean_ctor_set(x_2436, 1, x_2434);
x_2437 = lean_array_push(x_2429, x_2436);
x_2438 = lean_array_push(x_2437, x_2428);
x_2439 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2421);
x_2440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2440, 0, x_2421);
lean_ctor_set(x_2440, 1, x_2439);
x_2441 = lean_array_push(x_2438, x_2440);
x_2442 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2421);
x_2443 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2443, 0, x_2421);
lean_ctor_set(x_2443, 1, x_2442);
x_2444 = lean_array_push(x_2426, x_2443);
lean_inc(x_14);
x_2445 = lean_array_push(x_2426, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2446 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2446 = lean_box(0);
}
if (lean_is_scalar(x_2446)) {
 x_2447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2447 = x_2446;
}
lean_ctor_set(x_2447, 0, x_2435);
lean_ctor_set(x_2447, 1, x_2445);
x_2448 = lean_array_push(x_2444, x_2447);
x_2449 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2450 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2450, 0, x_2421);
lean_ctor_set(x_2450, 1, x_2449);
x_2451 = lean_array_push(x_2448, x_2450);
x_2452 = lean_array_push(x_2451, x_2419);
x_2453 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2454, 0, x_2453);
lean_ctor_set(x_2454, 1, x_2452);
x_2455 = lean_array_push(x_2426, x_2454);
x_2456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2456, 0, x_2435);
lean_ctor_set(x_2456, 1, x_2455);
x_2457 = lean_array_push(x_2426, x_2456);
x_2458 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2459, 0, x_2458);
lean_ctor_set(x_2459, 1, x_2457);
x_2460 = lean_array_push(x_2441, x_2459);
x_2461 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2462, 0, x_2461);
lean_ctor_set(x_2462, 1, x_2460);
x_2463 = 1;
x_2464 = lean_box(x_2463);
x_2465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2465, 0, x_2462);
lean_ctor_set(x_2465, 1, x_2464);
lean_ctor_set(x_2304, 1, x_2465);
if (lean_is_scalar(x_2423)) {
 x_2466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2466 = x_2423;
}
lean_ctor_set(x_2466, 0, x_2304);
lean_ctor_set(x_2466, 1, x_2422);
return x_2466;
}
}
else
{
lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; uint8_t x_2513; lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; 
x_2467 = lean_ctor_get(x_2304, 0);
lean_inc(x_2467);
lean_dec(x_2304);
x_2468 = lean_ctor_get(x_2305, 0);
lean_inc(x_2468);
if (lean_is_exclusive(x_2305)) {
 lean_ctor_release(x_2305, 0);
 lean_ctor_release(x_2305, 1);
 x_2469 = x_2305;
} else {
 lean_dec_ref(x_2305);
 x_2469 = lean_box(0);
}
x_2470 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2306);
lean_dec(x_5);
x_2471 = lean_ctor_get(x_2470, 0);
lean_inc(x_2471);
x_2472 = lean_ctor_get(x_2470, 1);
lean_inc(x_2472);
if (lean_is_exclusive(x_2470)) {
 lean_ctor_release(x_2470, 0);
 lean_ctor_release(x_2470, 1);
 x_2473 = x_2470;
} else {
 lean_dec_ref(x_2470);
 x_2473 = lean_box(0);
}
x_2474 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2471);
x_2475 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2475, 0, x_2471);
lean_ctor_set(x_2475, 1, x_2474);
x_2476 = l_Array_empty___closed__1;
x_2477 = lean_array_push(x_2476, x_2475);
x_2478 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2479 = lean_array_push(x_2477, x_2478);
x_2480 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2481 = lean_array_push(x_2480, x_2296);
x_2482 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2483, 0, x_2482);
lean_ctor_set(x_2483, 1, x_2481);
x_2484 = lean_array_push(x_2476, x_2483);
x_2485 = l_Lean_nullKind___closed__2;
x_2486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2486, 0, x_2485);
lean_ctor_set(x_2486, 1, x_2484);
x_2487 = lean_array_push(x_2479, x_2486);
x_2488 = lean_array_push(x_2487, x_2478);
x_2489 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2471);
x_2490 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2490, 0, x_2471);
lean_ctor_set(x_2490, 1, x_2489);
x_2491 = lean_array_push(x_2488, x_2490);
x_2492 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2471);
x_2493 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2493, 0, x_2471);
lean_ctor_set(x_2493, 1, x_2492);
x_2494 = lean_array_push(x_2476, x_2493);
lean_inc(x_14);
x_2495 = lean_array_push(x_2476, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2496 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2496 = lean_box(0);
}
if (lean_is_scalar(x_2496)) {
 x_2497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2497 = x_2496;
}
lean_ctor_set(x_2497, 0, x_2485);
lean_ctor_set(x_2497, 1, x_2495);
x_2498 = lean_array_push(x_2494, x_2497);
x_2499 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2500 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2500, 0, x_2471);
lean_ctor_set(x_2500, 1, x_2499);
x_2501 = lean_array_push(x_2498, x_2500);
x_2502 = lean_array_push(x_2501, x_2468);
x_2503 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2504, 0, x_2503);
lean_ctor_set(x_2504, 1, x_2502);
x_2505 = lean_array_push(x_2476, x_2504);
x_2506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2506, 0, x_2485);
lean_ctor_set(x_2506, 1, x_2505);
x_2507 = lean_array_push(x_2476, x_2506);
x_2508 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2509, 0, x_2508);
lean_ctor_set(x_2509, 1, x_2507);
x_2510 = lean_array_push(x_2491, x_2509);
x_2511 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2512, 0, x_2511);
lean_ctor_set(x_2512, 1, x_2510);
x_2513 = 1;
x_2514 = lean_box(x_2513);
if (lean_is_scalar(x_2469)) {
 x_2515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2515 = x_2469;
}
lean_ctor_set(x_2515, 0, x_2512);
lean_ctor_set(x_2515, 1, x_2514);
x_2516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2516, 0, x_2467);
lean_ctor_set(x_2516, 1, x_2515);
if (lean_is_scalar(x_2473)) {
 x_2517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2517 = x_2473;
}
lean_ctor_set(x_2517, 0, x_2516);
lean_ctor_set(x_2517, 1, x_2472);
return x_2517;
}
}
}
else
{
lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; uint8_t x_2530; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_inc(x_5);
x_2518 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2519 = lean_ctor_get(x_2518, 0);
lean_inc(x_2519);
x_2520 = lean_ctor_get(x_2518, 1);
lean_inc(x_2520);
lean_dec(x_2518);
x_2521 = lean_unsigned_to_nat(1u);
x_2522 = lean_nat_add(x_3, x_2521);
lean_dec(x_3);
x_2523 = l_Lean_mkHole(x_14);
lean_inc(x_2519);
x_2524 = l_Lean_Elab_Term_mkExplicitBinder(x_2519, x_2523);
x_2525 = lean_array_push(x_4, x_2524);
lean_inc(x_5);
x_2526 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2522, x_2525, x_5, x_2520);
x_2527 = lean_ctor_get(x_2526, 0);
lean_inc(x_2527);
x_2528 = lean_ctor_get(x_2527, 1);
lean_inc(x_2528);
x_2529 = lean_ctor_get(x_2526, 1);
lean_inc(x_2529);
lean_dec(x_2526);
x_2530 = !lean_is_exclusive(x_2527);
if (x_2530 == 0)
{
lean_object* x_2531; uint8_t x_2532; 
x_2531 = lean_ctor_get(x_2527, 1);
lean_dec(x_2531);
x_2532 = !lean_is_exclusive(x_2528);
if (x_2532 == 0)
{
lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; uint8_t x_2536; 
x_2533 = lean_ctor_get(x_2528, 0);
x_2534 = lean_ctor_get(x_2528, 1);
lean_dec(x_2534);
x_2535 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2529);
lean_dec(x_5);
x_2536 = !lean_is_exclusive(x_2535);
if (x_2536 == 0)
{
lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; uint8_t x_2560; 
x_2537 = lean_ctor_get(x_2535, 0);
x_2538 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2537);
x_2539 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2539, 0, x_2537);
lean_ctor_set(x_2539, 1, x_2538);
x_2540 = l_Array_empty___closed__1;
x_2541 = lean_array_push(x_2540, x_2539);
x_2542 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2543 = lean_array_push(x_2541, x_2542);
x_2544 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2545 = lean_array_push(x_2544, x_2519);
x_2546 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2547, 0, x_2546);
lean_ctor_set(x_2547, 1, x_2545);
x_2548 = lean_array_push(x_2540, x_2547);
x_2549 = l_Lean_nullKind___closed__2;
x_2550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2550, 0, x_2549);
lean_ctor_set(x_2550, 1, x_2548);
x_2551 = lean_array_push(x_2543, x_2550);
x_2552 = lean_array_push(x_2551, x_2542);
x_2553 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2537);
x_2554 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2554, 0, x_2537);
lean_ctor_set(x_2554, 1, x_2553);
x_2555 = lean_array_push(x_2552, x_2554);
x_2556 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2537);
x_2557 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2557, 0, x_2537);
lean_ctor_set(x_2557, 1, x_2556);
x_2558 = lean_array_push(x_2540, x_2557);
lean_inc(x_14);
x_2559 = lean_array_push(x_2540, x_14);
x_2560 = !lean_is_exclusive(x_14);
if (x_2560 == 0)
{
lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; uint8_t x_2578; lean_object* x_2579; 
x_2561 = lean_ctor_get(x_14, 1);
lean_dec(x_2561);
x_2562 = lean_ctor_get(x_14, 0);
lean_dec(x_2562);
lean_ctor_set(x_14, 1, x_2559);
lean_ctor_set(x_14, 0, x_2549);
x_2563 = lean_array_push(x_2558, x_14);
x_2564 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2565 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2565, 0, x_2537);
lean_ctor_set(x_2565, 1, x_2564);
x_2566 = lean_array_push(x_2563, x_2565);
x_2567 = lean_array_push(x_2566, x_2533);
x_2568 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2569, 0, x_2568);
lean_ctor_set(x_2569, 1, x_2567);
x_2570 = lean_array_push(x_2540, x_2569);
x_2571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2571, 0, x_2549);
lean_ctor_set(x_2571, 1, x_2570);
x_2572 = lean_array_push(x_2540, x_2571);
x_2573 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2574, 0, x_2573);
lean_ctor_set(x_2574, 1, x_2572);
x_2575 = lean_array_push(x_2555, x_2574);
x_2576 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2577, 0, x_2576);
lean_ctor_set(x_2577, 1, x_2575);
x_2578 = 1;
x_2579 = lean_box(x_2578);
lean_ctor_set(x_2528, 1, x_2579);
lean_ctor_set(x_2528, 0, x_2577);
lean_ctor_set(x_2535, 0, x_2527);
return x_2535;
}
else
{
lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; uint8_t x_2596; lean_object* x_2597; 
lean_dec(x_14);
x_2580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2580, 0, x_2549);
lean_ctor_set(x_2580, 1, x_2559);
x_2581 = lean_array_push(x_2558, x_2580);
x_2582 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2583 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2583, 0, x_2537);
lean_ctor_set(x_2583, 1, x_2582);
x_2584 = lean_array_push(x_2581, x_2583);
x_2585 = lean_array_push(x_2584, x_2533);
x_2586 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2587, 0, x_2586);
lean_ctor_set(x_2587, 1, x_2585);
x_2588 = lean_array_push(x_2540, x_2587);
x_2589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2589, 0, x_2549);
lean_ctor_set(x_2589, 1, x_2588);
x_2590 = lean_array_push(x_2540, x_2589);
x_2591 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2592, 0, x_2591);
lean_ctor_set(x_2592, 1, x_2590);
x_2593 = lean_array_push(x_2555, x_2592);
x_2594 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2595, 0, x_2594);
lean_ctor_set(x_2595, 1, x_2593);
x_2596 = 1;
x_2597 = lean_box(x_2596);
lean_ctor_set(x_2528, 1, x_2597);
lean_ctor_set(x_2528, 0, x_2595);
lean_ctor_set(x_2535, 0, x_2527);
return x_2535;
}
}
else
{
lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; uint8_t x_2639; lean_object* x_2640; lean_object* x_2641; 
x_2598 = lean_ctor_get(x_2535, 0);
x_2599 = lean_ctor_get(x_2535, 1);
lean_inc(x_2599);
lean_inc(x_2598);
lean_dec(x_2535);
x_2600 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2598);
x_2601 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2601, 0, x_2598);
lean_ctor_set(x_2601, 1, x_2600);
x_2602 = l_Array_empty___closed__1;
x_2603 = lean_array_push(x_2602, x_2601);
x_2604 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2605 = lean_array_push(x_2603, x_2604);
x_2606 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2607 = lean_array_push(x_2606, x_2519);
x_2608 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2609, 0, x_2608);
lean_ctor_set(x_2609, 1, x_2607);
x_2610 = lean_array_push(x_2602, x_2609);
x_2611 = l_Lean_nullKind___closed__2;
x_2612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2612, 0, x_2611);
lean_ctor_set(x_2612, 1, x_2610);
x_2613 = lean_array_push(x_2605, x_2612);
x_2614 = lean_array_push(x_2613, x_2604);
x_2615 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2598);
x_2616 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2616, 0, x_2598);
lean_ctor_set(x_2616, 1, x_2615);
x_2617 = lean_array_push(x_2614, x_2616);
x_2618 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2598);
x_2619 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2619, 0, x_2598);
lean_ctor_set(x_2619, 1, x_2618);
x_2620 = lean_array_push(x_2602, x_2619);
lean_inc(x_14);
x_2621 = lean_array_push(x_2602, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2622 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2622 = lean_box(0);
}
if (lean_is_scalar(x_2622)) {
 x_2623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2623 = x_2622;
}
lean_ctor_set(x_2623, 0, x_2611);
lean_ctor_set(x_2623, 1, x_2621);
x_2624 = lean_array_push(x_2620, x_2623);
x_2625 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2626 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2626, 0, x_2598);
lean_ctor_set(x_2626, 1, x_2625);
x_2627 = lean_array_push(x_2624, x_2626);
x_2628 = lean_array_push(x_2627, x_2533);
x_2629 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2630, 0, x_2629);
lean_ctor_set(x_2630, 1, x_2628);
x_2631 = lean_array_push(x_2602, x_2630);
x_2632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2632, 0, x_2611);
lean_ctor_set(x_2632, 1, x_2631);
x_2633 = lean_array_push(x_2602, x_2632);
x_2634 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2635, 0, x_2634);
lean_ctor_set(x_2635, 1, x_2633);
x_2636 = lean_array_push(x_2617, x_2635);
x_2637 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2638, 0, x_2637);
lean_ctor_set(x_2638, 1, x_2636);
x_2639 = 1;
x_2640 = lean_box(x_2639);
lean_ctor_set(x_2528, 1, x_2640);
lean_ctor_set(x_2528, 0, x_2638);
x_2641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2641, 0, x_2527);
lean_ctor_set(x_2641, 1, x_2599);
return x_2641;
}
}
else
{
lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; uint8_t x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; 
x_2642 = lean_ctor_get(x_2528, 0);
lean_inc(x_2642);
lean_dec(x_2528);
x_2643 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2529);
lean_dec(x_5);
x_2644 = lean_ctor_get(x_2643, 0);
lean_inc(x_2644);
x_2645 = lean_ctor_get(x_2643, 1);
lean_inc(x_2645);
if (lean_is_exclusive(x_2643)) {
 lean_ctor_release(x_2643, 0);
 lean_ctor_release(x_2643, 1);
 x_2646 = x_2643;
} else {
 lean_dec_ref(x_2643);
 x_2646 = lean_box(0);
}
x_2647 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2644);
x_2648 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2648, 0, x_2644);
lean_ctor_set(x_2648, 1, x_2647);
x_2649 = l_Array_empty___closed__1;
x_2650 = lean_array_push(x_2649, x_2648);
x_2651 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2652 = lean_array_push(x_2650, x_2651);
x_2653 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2654 = lean_array_push(x_2653, x_2519);
x_2655 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2656, 0, x_2655);
lean_ctor_set(x_2656, 1, x_2654);
x_2657 = lean_array_push(x_2649, x_2656);
x_2658 = l_Lean_nullKind___closed__2;
x_2659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2659, 0, x_2658);
lean_ctor_set(x_2659, 1, x_2657);
x_2660 = lean_array_push(x_2652, x_2659);
x_2661 = lean_array_push(x_2660, x_2651);
x_2662 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2644);
x_2663 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2663, 0, x_2644);
lean_ctor_set(x_2663, 1, x_2662);
x_2664 = lean_array_push(x_2661, x_2663);
x_2665 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2644);
x_2666 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2666, 0, x_2644);
lean_ctor_set(x_2666, 1, x_2665);
x_2667 = lean_array_push(x_2649, x_2666);
lean_inc(x_14);
x_2668 = lean_array_push(x_2649, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2669 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2669 = lean_box(0);
}
if (lean_is_scalar(x_2669)) {
 x_2670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2670 = x_2669;
}
lean_ctor_set(x_2670, 0, x_2658);
lean_ctor_set(x_2670, 1, x_2668);
x_2671 = lean_array_push(x_2667, x_2670);
x_2672 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2673 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2673, 0, x_2644);
lean_ctor_set(x_2673, 1, x_2672);
x_2674 = lean_array_push(x_2671, x_2673);
x_2675 = lean_array_push(x_2674, x_2642);
x_2676 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2677, 0, x_2676);
lean_ctor_set(x_2677, 1, x_2675);
x_2678 = lean_array_push(x_2649, x_2677);
x_2679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2679, 0, x_2658);
lean_ctor_set(x_2679, 1, x_2678);
x_2680 = lean_array_push(x_2649, x_2679);
x_2681 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2682, 0, x_2681);
lean_ctor_set(x_2682, 1, x_2680);
x_2683 = lean_array_push(x_2664, x_2682);
x_2684 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2685 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2685, 0, x_2684);
lean_ctor_set(x_2685, 1, x_2683);
x_2686 = 1;
x_2687 = lean_box(x_2686);
x_2688 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2688, 0, x_2685);
lean_ctor_set(x_2688, 1, x_2687);
lean_ctor_set(x_2527, 1, x_2688);
if (lean_is_scalar(x_2646)) {
 x_2689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2689 = x_2646;
}
lean_ctor_set(x_2689, 0, x_2527);
lean_ctor_set(x_2689, 1, x_2645);
return x_2689;
}
}
else
{
lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; uint8_t x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; 
x_2690 = lean_ctor_get(x_2527, 0);
lean_inc(x_2690);
lean_dec(x_2527);
x_2691 = lean_ctor_get(x_2528, 0);
lean_inc(x_2691);
if (lean_is_exclusive(x_2528)) {
 lean_ctor_release(x_2528, 0);
 lean_ctor_release(x_2528, 1);
 x_2692 = x_2528;
} else {
 lean_dec_ref(x_2528);
 x_2692 = lean_box(0);
}
x_2693 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2529);
lean_dec(x_5);
x_2694 = lean_ctor_get(x_2693, 0);
lean_inc(x_2694);
x_2695 = lean_ctor_get(x_2693, 1);
lean_inc(x_2695);
if (lean_is_exclusive(x_2693)) {
 lean_ctor_release(x_2693, 0);
 lean_ctor_release(x_2693, 1);
 x_2696 = x_2693;
} else {
 lean_dec_ref(x_2693);
 x_2696 = lean_box(0);
}
x_2697 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2694);
x_2698 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2698, 0, x_2694);
lean_ctor_set(x_2698, 1, x_2697);
x_2699 = l_Array_empty___closed__1;
x_2700 = lean_array_push(x_2699, x_2698);
x_2701 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2702 = lean_array_push(x_2700, x_2701);
x_2703 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2704 = lean_array_push(x_2703, x_2519);
x_2705 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2706, 0, x_2705);
lean_ctor_set(x_2706, 1, x_2704);
x_2707 = lean_array_push(x_2699, x_2706);
x_2708 = l_Lean_nullKind___closed__2;
x_2709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2709, 0, x_2708);
lean_ctor_set(x_2709, 1, x_2707);
x_2710 = lean_array_push(x_2702, x_2709);
x_2711 = lean_array_push(x_2710, x_2701);
x_2712 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2694);
x_2713 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2713, 0, x_2694);
lean_ctor_set(x_2713, 1, x_2712);
x_2714 = lean_array_push(x_2711, x_2713);
x_2715 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2694);
x_2716 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2716, 0, x_2694);
lean_ctor_set(x_2716, 1, x_2715);
x_2717 = lean_array_push(x_2699, x_2716);
lean_inc(x_14);
x_2718 = lean_array_push(x_2699, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2719 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2719 = lean_box(0);
}
if (lean_is_scalar(x_2719)) {
 x_2720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2720 = x_2719;
}
lean_ctor_set(x_2720, 0, x_2708);
lean_ctor_set(x_2720, 1, x_2718);
x_2721 = lean_array_push(x_2717, x_2720);
x_2722 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2723 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2723, 0, x_2694);
lean_ctor_set(x_2723, 1, x_2722);
x_2724 = lean_array_push(x_2721, x_2723);
x_2725 = lean_array_push(x_2724, x_2691);
x_2726 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2727, 0, x_2726);
lean_ctor_set(x_2727, 1, x_2725);
x_2728 = lean_array_push(x_2699, x_2727);
x_2729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2729, 0, x_2708);
lean_ctor_set(x_2729, 1, x_2728);
x_2730 = lean_array_push(x_2699, x_2729);
x_2731 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2732, 0, x_2731);
lean_ctor_set(x_2732, 1, x_2730);
x_2733 = lean_array_push(x_2714, x_2732);
x_2734 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2735 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2735, 0, x_2734);
lean_ctor_set(x_2735, 1, x_2733);
x_2736 = 1;
x_2737 = lean_box(x_2736);
if (lean_is_scalar(x_2692)) {
 x_2738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2738 = x_2692;
}
lean_ctor_set(x_2738, 0, x_2735);
lean_ctor_set(x_2738, 1, x_2737);
x_2739 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2739, 0, x_2690);
lean_ctor_set(x_2739, 1, x_2738);
if (lean_is_scalar(x_2696)) {
 x_2740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2740 = x_2696;
}
lean_ctor_set(x_2740, 0, x_2739);
lean_ctor_set(x_2740, 1, x_2695);
return x_2740;
}
}
}
else
{
lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; uint8_t x_2753; 
lean_dec(x_216);
lean_dec(x_215);
lean_inc(x_5);
x_2741 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2742 = lean_ctor_get(x_2741, 0);
lean_inc(x_2742);
x_2743 = lean_ctor_get(x_2741, 1);
lean_inc(x_2743);
lean_dec(x_2741);
x_2744 = lean_unsigned_to_nat(1u);
x_2745 = lean_nat_add(x_3, x_2744);
lean_dec(x_3);
x_2746 = l_Lean_mkHole(x_14);
lean_inc(x_2742);
x_2747 = l_Lean_Elab_Term_mkExplicitBinder(x_2742, x_2746);
x_2748 = lean_array_push(x_4, x_2747);
lean_inc(x_5);
x_2749 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2745, x_2748, x_5, x_2743);
x_2750 = lean_ctor_get(x_2749, 0);
lean_inc(x_2750);
x_2751 = lean_ctor_get(x_2750, 1);
lean_inc(x_2751);
x_2752 = lean_ctor_get(x_2749, 1);
lean_inc(x_2752);
lean_dec(x_2749);
x_2753 = !lean_is_exclusive(x_2750);
if (x_2753 == 0)
{
lean_object* x_2754; uint8_t x_2755; 
x_2754 = lean_ctor_get(x_2750, 1);
lean_dec(x_2754);
x_2755 = !lean_is_exclusive(x_2751);
if (x_2755 == 0)
{
lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; uint8_t x_2759; 
x_2756 = lean_ctor_get(x_2751, 0);
x_2757 = lean_ctor_get(x_2751, 1);
lean_dec(x_2757);
x_2758 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2752);
lean_dec(x_5);
x_2759 = !lean_is_exclusive(x_2758);
if (x_2759 == 0)
{
lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; uint8_t x_2783; 
x_2760 = lean_ctor_get(x_2758, 0);
x_2761 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2760);
x_2762 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2762, 0, x_2760);
lean_ctor_set(x_2762, 1, x_2761);
x_2763 = l_Array_empty___closed__1;
x_2764 = lean_array_push(x_2763, x_2762);
x_2765 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2766 = lean_array_push(x_2764, x_2765);
x_2767 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2768 = lean_array_push(x_2767, x_2742);
x_2769 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2770, 0, x_2769);
lean_ctor_set(x_2770, 1, x_2768);
x_2771 = lean_array_push(x_2763, x_2770);
x_2772 = l_Lean_nullKind___closed__2;
x_2773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2773, 0, x_2772);
lean_ctor_set(x_2773, 1, x_2771);
x_2774 = lean_array_push(x_2766, x_2773);
x_2775 = lean_array_push(x_2774, x_2765);
x_2776 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2760);
x_2777 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2777, 0, x_2760);
lean_ctor_set(x_2777, 1, x_2776);
x_2778 = lean_array_push(x_2775, x_2777);
x_2779 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2760);
x_2780 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2780, 0, x_2760);
lean_ctor_set(x_2780, 1, x_2779);
x_2781 = lean_array_push(x_2763, x_2780);
lean_inc(x_14);
x_2782 = lean_array_push(x_2763, x_14);
x_2783 = !lean_is_exclusive(x_14);
if (x_2783 == 0)
{
lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; uint8_t x_2801; lean_object* x_2802; 
x_2784 = lean_ctor_get(x_14, 1);
lean_dec(x_2784);
x_2785 = lean_ctor_get(x_14, 0);
lean_dec(x_2785);
lean_ctor_set(x_14, 1, x_2782);
lean_ctor_set(x_14, 0, x_2772);
x_2786 = lean_array_push(x_2781, x_14);
x_2787 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2788 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2788, 0, x_2760);
lean_ctor_set(x_2788, 1, x_2787);
x_2789 = lean_array_push(x_2786, x_2788);
x_2790 = lean_array_push(x_2789, x_2756);
x_2791 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2792, 0, x_2791);
lean_ctor_set(x_2792, 1, x_2790);
x_2793 = lean_array_push(x_2763, x_2792);
x_2794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2794, 0, x_2772);
lean_ctor_set(x_2794, 1, x_2793);
x_2795 = lean_array_push(x_2763, x_2794);
x_2796 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2797, 0, x_2796);
lean_ctor_set(x_2797, 1, x_2795);
x_2798 = lean_array_push(x_2778, x_2797);
x_2799 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2800, 0, x_2799);
lean_ctor_set(x_2800, 1, x_2798);
x_2801 = 1;
x_2802 = lean_box(x_2801);
lean_ctor_set(x_2751, 1, x_2802);
lean_ctor_set(x_2751, 0, x_2800);
lean_ctor_set(x_2758, 0, x_2750);
return x_2758;
}
else
{
lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; uint8_t x_2819; lean_object* x_2820; 
lean_dec(x_14);
x_2803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2803, 0, x_2772);
lean_ctor_set(x_2803, 1, x_2782);
x_2804 = lean_array_push(x_2781, x_2803);
x_2805 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2806 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2806, 0, x_2760);
lean_ctor_set(x_2806, 1, x_2805);
x_2807 = lean_array_push(x_2804, x_2806);
x_2808 = lean_array_push(x_2807, x_2756);
x_2809 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2810, 0, x_2809);
lean_ctor_set(x_2810, 1, x_2808);
x_2811 = lean_array_push(x_2763, x_2810);
x_2812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2812, 0, x_2772);
lean_ctor_set(x_2812, 1, x_2811);
x_2813 = lean_array_push(x_2763, x_2812);
x_2814 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2815, 0, x_2814);
lean_ctor_set(x_2815, 1, x_2813);
x_2816 = lean_array_push(x_2778, x_2815);
x_2817 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2818, 0, x_2817);
lean_ctor_set(x_2818, 1, x_2816);
x_2819 = 1;
x_2820 = lean_box(x_2819);
lean_ctor_set(x_2751, 1, x_2820);
lean_ctor_set(x_2751, 0, x_2818);
lean_ctor_set(x_2758, 0, x_2750);
return x_2758;
}
}
else
{
lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; uint8_t x_2862; lean_object* x_2863; lean_object* x_2864; 
x_2821 = lean_ctor_get(x_2758, 0);
x_2822 = lean_ctor_get(x_2758, 1);
lean_inc(x_2822);
lean_inc(x_2821);
lean_dec(x_2758);
x_2823 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2821);
x_2824 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2824, 0, x_2821);
lean_ctor_set(x_2824, 1, x_2823);
x_2825 = l_Array_empty___closed__1;
x_2826 = lean_array_push(x_2825, x_2824);
x_2827 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2828 = lean_array_push(x_2826, x_2827);
x_2829 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2830 = lean_array_push(x_2829, x_2742);
x_2831 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2832, 0, x_2831);
lean_ctor_set(x_2832, 1, x_2830);
x_2833 = lean_array_push(x_2825, x_2832);
x_2834 = l_Lean_nullKind___closed__2;
x_2835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2835, 0, x_2834);
lean_ctor_set(x_2835, 1, x_2833);
x_2836 = lean_array_push(x_2828, x_2835);
x_2837 = lean_array_push(x_2836, x_2827);
x_2838 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2821);
x_2839 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2839, 0, x_2821);
lean_ctor_set(x_2839, 1, x_2838);
x_2840 = lean_array_push(x_2837, x_2839);
x_2841 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2821);
x_2842 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2842, 0, x_2821);
lean_ctor_set(x_2842, 1, x_2841);
x_2843 = lean_array_push(x_2825, x_2842);
lean_inc(x_14);
x_2844 = lean_array_push(x_2825, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2845 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2845 = lean_box(0);
}
if (lean_is_scalar(x_2845)) {
 x_2846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2846 = x_2845;
}
lean_ctor_set(x_2846, 0, x_2834);
lean_ctor_set(x_2846, 1, x_2844);
x_2847 = lean_array_push(x_2843, x_2846);
x_2848 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2849 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2849, 0, x_2821);
lean_ctor_set(x_2849, 1, x_2848);
x_2850 = lean_array_push(x_2847, x_2849);
x_2851 = lean_array_push(x_2850, x_2756);
x_2852 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2853, 0, x_2852);
lean_ctor_set(x_2853, 1, x_2851);
x_2854 = lean_array_push(x_2825, x_2853);
x_2855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2855, 0, x_2834);
lean_ctor_set(x_2855, 1, x_2854);
x_2856 = lean_array_push(x_2825, x_2855);
x_2857 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2858 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2858, 0, x_2857);
lean_ctor_set(x_2858, 1, x_2856);
x_2859 = lean_array_push(x_2840, x_2858);
x_2860 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2861, 0, x_2860);
lean_ctor_set(x_2861, 1, x_2859);
x_2862 = 1;
x_2863 = lean_box(x_2862);
lean_ctor_set(x_2751, 1, x_2863);
lean_ctor_set(x_2751, 0, x_2861);
x_2864 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2864, 0, x_2750);
lean_ctor_set(x_2864, 1, x_2822);
return x_2864;
}
}
else
{
lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; uint8_t x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; 
x_2865 = lean_ctor_get(x_2751, 0);
lean_inc(x_2865);
lean_dec(x_2751);
x_2866 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2752);
lean_dec(x_5);
x_2867 = lean_ctor_get(x_2866, 0);
lean_inc(x_2867);
x_2868 = lean_ctor_get(x_2866, 1);
lean_inc(x_2868);
if (lean_is_exclusive(x_2866)) {
 lean_ctor_release(x_2866, 0);
 lean_ctor_release(x_2866, 1);
 x_2869 = x_2866;
} else {
 lean_dec_ref(x_2866);
 x_2869 = lean_box(0);
}
x_2870 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2867);
x_2871 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2871, 0, x_2867);
lean_ctor_set(x_2871, 1, x_2870);
x_2872 = l_Array_empty___closed__1;
x_2873 = lean_array_push(x_2872, x_2871);
x_2874 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2875 = lean_array_push(x_2873, x_2874);
x_2876 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2877 = lean_array_push(x_2876, x_2742);
x_2878 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2879, 0, x_2878);
lean_ctor_set(x_2879, 1, x_2877);
x_2880 = lean_array_push(x_2872, x_2879);
x_2881 = l_Lean_nullKind___closed__2;
x_2882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2882, 0, x_2881);
lean_ctor_set(x_2882, 1, x_2880);
x_2883 = lean_array_push(x_2875, x_2882);
x_2884 = lean_array_push(x_2883, x_2874);
x_2885 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2867);
x_2886 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2886, 0, x_2867);
lean_ctor_set(x_2886, 1, x_2885);
x_2887 = lean_array_push(x_2884, x_2886);
x_2888 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2867);
x_2889 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2889, 0, x_2867);
lean_ctor_set(x_2889, 1, x_2888);
x_2890 = lean_array_push(x_2872, x_2889);
lean_inc(x_14);
x_2891 = lean_array_push(x_2872, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2892 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2892 = lean_box(0);
}
if (lean_is_scalar(x_2892)) {
 x_2893 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2893 = x_2892;
}
lean_ctor_set(x_2893, 0, x_2881);
lean_ctor_set(x_2893, 1, x_2891);
x_2894 = lean_array_push(x_2890, x_2893);
x_2895 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2896 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2896, 0, x_2867);
lean_ctor_set(x_2896, 1, x_2895);
x_2897 = lean_array_push(x_2894, x_2896);
x_2898 = lean_array_push(x_2897, x_2865);
x_2899 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2900, 0, x_2899);
lean_ctor_set(x_2900, 1, x_2898);
x_2901 = lean_array_push(x_2872, x_2900);
x_2902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2902, 0, x_2881);
lean_ctor_set(x_2902, 1, x_2901);
x_2903 = lean_array_push(x_2872, x_2902);
x_2904 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2905 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2905, 0, x_2904);
lean_ctor_set(x_2905, 1, x_2903);
x_2906 = lean_array_push(x_2887, x_2905);
x_2907 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2908, 0, x_2907);
lean_ctor_set(x_2908, 1, x_2906);
x_2909 = 1;
x_2910 = lean_box(x_2909);
x_2911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2911, 0, x_2908);
lean_ctor_set(x_2911, 1, x_2910);
lean_ctor_set(x_2750, 1, x_2911);
if (lean_is_scalar(x_2869)) {
 x_2912 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2912 = x_2869;
}
lean_ctor_set(x_2912, 0, x_2750);
lean_ctor_set(x_2912, 1, x_2868);
return x_2912;
}
}
else
{
lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; uint8_t x_2959; lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; 
x_2913 = lean_ctor_get(x_2750, 0);
lean_inc(x_2913);
lean_dec(x_2750);
x_2914 = lean_ctor_get(x_2751, 0);
lean_inc(x_2914);
if (lean_is_exclusive(x_2751)) {
 lean_ctor_release(x_2751, 0);
 lean_ctor_release(x_2751, 1);
 x_2915 = x_2751;
} else {
 lean_dec_ref(x_2751);
 x_2915 = lean_box(0);
}
x_2916 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2752);
lean_dec(x_5);
x_2917 = lean_ctor_get(x_2916, 0);
lean_inc(x_2917);
x_2918 = lean_ctor_get(x_2916, 1);
lean_inc(x_2918);
if (lean_is_exclusive(x_2916)) {
 lean_ctor_release(x_2916, 0);
 lean_ctor_release(x_2916, 1);
 x_2919 = x_2916;
} else {
 lean_dec_ref(x_2916);
 x_2919 = lean_box(0);
}
x_2920 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2917);
x_2921 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2921, 0, x_2917);
lean_ctor_set(x_2921, 1, x_2920);
x_2922 = l_Array_empty___closed__1;
x_2923 = lean_array_push(x_2922, x_2921);
x_2924 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2925 = lean_array_push(x_2923, x_2924);
x_2926 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2927 = lean_array_push(x_2926, x_2742);
x_2928 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2929, 0, x_2928);
lean_ctor_set(x_2929, 1, x_2927);
x_2930 = lean_array_push(x_2922, x_2929);
x_2931 = l_Lean_nullKind___closed__2;
x_2932 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2932, 0, x_2931);
lean_ctor_set(x_2932, 1, x_2930);
x_2933 = lean_array_push(x_2925, x_2932);
x_2934 = lean_array_push(x_2933, x_2924);
x_2935 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2917);
x_2936 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2936, 0, x_2917);
lean_ctor_set(x_2936, 1, x_2935);
x_2937 = lean_array_push(x_2934, x_2936);
x_2938 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2917);
x_2939 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2939, 0, x_2917);
lean_ctor_set(x_2939, 1, x_2938);
x_2940 = lean_array_push(x_2922, x_2939);
lean_inc(x_14);
x_2941 = lean_array_push(x_2922, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_2942 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2942 = lean_box(0);
}
if (lean_is_scalar(x_2942)) {
 x_2943 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2943 = x_2942;
}
lean_ctor_set(x_2943, 0, x_2931);
lean_ctor_set(x_2943, 1, x_2941);
x_2944 = lean_array_push(x_2940, x_2943);
x_2945 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_2946 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2946, 0, x_2917);
lean_ctor_set(x_2946, 1, x_2945);
x_2947 = lean_array_push(x_2944, x_2946);
x_2948 = lean_array_push(x_2947, x_2914);
x_2949 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_2950 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2950, 0, x_2949);
lean_ctor_set(x_2950, 1, x_2948);
x_2951 = lean_array_push(x_2922, x_2950);
x_2952 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2952, 0, x_2931);
lean_ctor_set(x_2952, 1, x_2951);
x_2953 = lean_array_push(x_2922, x_2952);
x_2954 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_2955 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2955, 0, x_2954);
lean_ctor_set(x_2955, 1, x_2953);
x_2956 = lean_array_push(x_2937, x_2955);
x_2957 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_2958 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2958, 0, x_2957);
lean_ctor_set(x_2958, 1, x_2956);
x_2959 = 1;
x_2960 = lean_box(x_2959);
if (lean_is_scalar(x_2915)) {
 x_2961 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2961 = x_2915;
}
lean_ctor_set(x_2961, 0, x_2958);
lean_ctor_set(x_2961, 1, x_2960);
x_2962 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2962, 0, x_2913);
lean_ctor_set(x_2962, 1, x_2961);
if (lean_is_scalar(x_2919)) {
 x_2963 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2963 = x_2919;
}
lean_ctor_set(x_2963, 0, x_2962);
lean_ctor_set(x_2963, 1, x_2918);
return x_2963;
}
}
}
else
{
lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; uint8_t x_2976; 
lean_dec(x_215);
lean_inc(x_5);
x_2964 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2965 = lean_ctor_get(x_2964, 0);
lean_inc(x_2965);
x_2966 = lean_ctor_get(x_2964, 1);
lean_inc(x_2966);
lean_dec(x_2964);
x_2967 = lean_unsigned_to_nat(1u);
x_2968 = lean_nat_add(x_3, x_2967);
lean_dec(x_3);
x_2969 = l_Lean_mkHole(x_14);
lean_inc(x_2965);
x_2970 = l_Lean_Elab_Term_mkExplicitBinder(x_2965, x_2969);
x_2971 = lean_array_push(x_4, x_2970);
lean_inc(x_5);
x_2972 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2968, x_2971, x_5, x_2966);
x_2973 = lean_ctor_get(x_2972, 0);
lean_inc(x_2973);
x_2974 = lean_ctor_get(x_2973, 1);
lean_inc(x_2974);
x_2975 = lean_ctor_get(x_2972, 1);
lean_inc(x_2975);
lean_dec(x_2972);
x_2976 = !lean_is_exclusive(x_2973);
if (x_2976 == 0)
{
lean_object* x_2977; uint8_t x_2978; 
x_2977 = lean_ctor_get(x_2973, 1);
lean_dec(x_2977);
x_2978 = !lean_is_exclusive(x_2974);
if (x_2978 == 0)
{
lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; uint8_t x_2982; 
x_2979 = lean_ctor_get(x_2974, 0);
x_2980 = lean_ctor_get(x_2974, 1);
lean_dec(x_2980);
x_2981 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2975);
lean_dec(x_5);
x_2982 = !lean_is_exclusive(x_2981);
if (x_2982 == 0)
{
lean_object* x_2983; lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; uint8_t x_3006; 
x_2983 = lean_ctor_get(x_2981, 0);
x_2984 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_2983);
x_2985 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2985, 0, x_2983);
lean_ctor_set(x_2985, 1, x_2984);
x_2986 = l_Array_empty___closed__1;
x_2987 = lean_array_push(x_2986, x_2985);
x_2988 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_2989 = lean_array_push(x_2987, x_2988);
x_2990 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_2991 = lean_array_push(x_2990, x_2965);
x_2992 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_2993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2993, 0, x_2992);
lean_ctor_set(x_2993, 1, x_2991);
x_2994 = lean_array_push(x_2986, x_2993);
x_2995 = l_Lean_nullKind___closed__2;
x_2996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2996, 0, x_2995);
lean_ctor_set(x_2996, 1, x_2994);
x_2997 = lean_array_push(x_2989, x_2996);
x_2998 = lean_array_push(x_2997, x_2988);
x_2999 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_2983);
x_3000 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3000, 0, x_2983);
lean_ctor_set(x_3000, 1, x_2999);
x_3001 = lean_array_push(x_2998, x_3000);
x_3002 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_2983);
x_3003 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3003, 0, x_2983);
lean_ctor_set(x_3003, 1, x_3002);
x_3004 = lean_array_push(x_2986, x_3003);
lean_inc(x_14);
x_3005 = lean_array_push(x_2986, x_14);
x_3006 = !lean_is_exclusive(x_14);
if (x_3006 == 0)
{
lean_object* x_3007; lean_object* x_3008; lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; uint8_t x_3024; lean_object* x_3025; 
x_3007 = lean_ctor_get(x_14, 1);
lean_dec(x_3007);
x_3008 = lean_ctor_get(x_14, 0);
lean_dec(x_3008);
lean_ctor_set(x_14, 1, x_3005);
lean_ctor_set(x_14, 0, x_2995);
x_3009 = lean_array_push(x_3004, x_14);
x_3010 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3011 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3011, 0, x_2983);
lean_ctor_set(x_3011, 1, x_3010);
x_3012 = lean_array_push(x_3009, x_3011);
x_3013 = lean_array_push(x_3012, x_2979);
x_3014 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3015 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3015, 0, x_3014);
lean_ctor_set(x_3015, 1, x_3013);
x_3016 = lean_array_push(x_2986, x_3015);
x_3017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3017, 0, x_2995);
lean_ctor_set(x_3017, 1, x_3016);
x_3018 = lean_array_push(x_2986, x_3017);
x_3019 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3020, 0, x_3019);
lean_ctor_set(x_3020, 1, x_3018);
x_3021 = lean_array_push(x_3001, x_3020);
x_3022 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3023, 0, x_3022);
lean_ctor_set(x_3023, 1, x_3021);
x_3024 = 1;
x_3025 = lean_box(x_3024);
lean_ctor_set(x_2974, 1, x_3025);
lean_ctor_set(x_2974, 0, x_3023);
lean_ctor_set(x_2981, 0, x_2973);
return x_2981;
}
else
{
lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; uint8_t x_3042; lean_object* x_3043; 
lean_dec(x_14);
x_3026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3026, 0, x_2995);
lean_ctor_set(x_3026, 1, x_3005);
x_3027 = lean_array_push(x_3004, x_3026);
x_3028 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3029 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3029, 0, x_2983);
lean_ctor_set(x_3029, 1, x_3028);
x_3030 = lean_array_push(x_3027, x_3029);
x_3031 = lean_array_push(x_3030, x_2979);
x_3032 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3033 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3033, 0, x_3032);
lean_ctor_set(x_3033, 1, x_3031);
x_3034 = lean_array_push(x_2986, x_3033);
x_3035 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3035, 0, x_2995);
lean_ctor_set(x_3035, 1, x_3034);
x_3036 = lean_array_push(x_2986, x_3035);
x_3037 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3038, 0, x_3037);
lean_ctor_set(x_3038, 1, x_3036);
x_3039 = lean_array_push(x_3001, x_3038);
x_3040 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3041 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3041, 0, x_3040);
lean_ctor_set(x_3041, 1, x_3039);
x_3042 = 1;
x_3043 = lean_box(x_3042);
lean_ctor_set(x_2974, 1, x_3043);
lean_ctor_set(x_2974, 0, x_3041);
lean_ctor_set(x_2981, 0, x_2973);
return x_2981;
}
}
else
{
lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; lean_object* x_3083; lean_object* x_3084; uint8_t x_3085; lean_object* x_3086; lean_object* x_3087; 
x_3044 = lean_ctor_get(x_2981, 0);
x_3045 = lean_ctor_get(x_2981, 1);
lean_inc(x_3045);
lean_inc(x_3044);
lean_dec(x_2981);
x_3046 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3044);
x_3047 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3047, 0, x_3044);
lean_ctor_set(x_3047, 1, x_3046);
x_3048 = l_Array_empty___closed__1;
x_3049 = lean_array_push(x_3048, x_3047);
x_3050 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3051 = lean_array_push(x_3049, x_3050);
x_3052 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3053 = lean_array_push(x_3052, x_2965);
x_3054 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3055, 0, x_3054);
lean_ctor_set(x_3055, 1, x_3053);
x_3056 = lean_array_push(x_3048, x_3055);
x_3057 = l_Lean_nullKind___closed__2;
x_3058 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3058, 0, x_3057);
lean_ctor_set(x_3058, 1, x_3056);
x_3059 = lean_array_push(x_3051, x_3058);
x_3060 = lean_array_push(x_3059, x_3050);
x_3061 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3044);
x_3062 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3062, 0, x_3044);
lean_ctor_set(x_3062, 1, x_3061);
x_3063 = lean_array_push(x_3060, x_3062);
x_3064 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3044);
x_3065 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3065, 0, x_3044);
lean_ctor_set(x_3065, 1, x_3064);
x_3066 = lean_array_push(x_3048, x_3065);
lean_inc(x_14);
x_3067 = lean_array_push(x_3048, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3068 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3068 = lean_box(0);
}
if (lean_is_scalar(x_3068)) {
 x_3069 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3069 = x_3068;
}
lean_ctor_set(x_3069, 0, x_3057);
lean_ctor_set(x_3069, 1, x_3067);
x_3070 = lean_array_push(x_3066, x_3069);
x_3071 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3072 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3072, 0, x_3044);
lean_ctor_set(x_3072, 1, x_3071);
x_3073 = lean_array_push(x_3070, x_3072);
x_3074 = lean_array_push(x_3073, x_2979);
x_3075 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3076 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3076, 0, x_3075);
lean_ctor_set(x_3076, 1, x_3074);
x_3077 = lean_array_push(x_3048, x_3076);
x_3078 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3078, 0, x_3057);
lean_ctor_set(x_3078, 1, x_3077);
x_3079 = lean_array_push(x_3048, x_3078);
x_3080 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3081 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3081, 0, x_3080);
lean_ctor_set(x_3081, 1, x_3079);
x_3082 = lean_array_push(x_3063, x_3081);
x_3083 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3084, 0, x_3083);
lean_ctor_set(x_3084, 1, x_3082);
x_3085 = 1;
x_3086 = lean_box(x_3085);
lean_ctor_set(x_2974, 1, x_3086);
lean_ctor_set(x_2974, 0, x_3084);
x_3087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3087, 0, x_2973);
lean_ctor_set(x_3087, 1, x_3045);
return x_3087;
}
}
else
{
lean_object* x_3088; lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; uint8_t x_3132; lean_object* x_3133; lean_object* x_3134; lean_object* x_3135; 
x_3088 = lean_ctor_get(x_2974, 0);
lean_inc(x_3088);
lean_dec(x_2974);
x_3089 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2975);
lean_dec(x_5);
x_3090 = lean_ctor_get(x_3089, 0);
lean_inc(x_3090);
x_3091 = lean_ctor_get(x_3089, 1);
lean_inc(x_3091);
if (lean_is_exclusive(x_3089)) {
 lean_ctor_release(x_3089, 0);
 lean_ctor_release(x_3089, 1);
 x_3092 = x_3089;
} else {
 lean_dec_ref(x_3089);
 x_3092 = lean_box(0);
}
x_3093 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3090);
x_3094 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3094, 0, x_3090);
lean_ctor_set(x_3094, 1, x_3093);
x_3095 = l_Array_empty___closed__1;
x_3096 = lean_array_push(x_3095, x_3094);
x_3097 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3098 = lean_array_push(x_3096, x_3097);
x_3099 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3100 = lean_array_push(x_3099, x_2965);
x_3101 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3102, 0, x_3101);
lean_ctor_set(x_3102, 1, x_3100);
x_3103 = lean_array_push(x_3095, x_3102);
x_3104 = l_Lean_nullKind___closed__2;
x_3105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3105, 0, x_3104);
lean_ctor_set(x_3105, 1, x_3103);
x_3106 = lean_array_push(x_3098, x_3105);
x_3107 = lean_array_push(x_3106, x_3097);
x_3108 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3090);
x_3109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3109, 0, x_3090);
lean_ctor_set(x_3109, 1, x_3108);
x_3110 = lean_array_push(x_3107, x_3109);
x_3111 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3090);
x_3112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3112, 0, x_3090);
lean_ctor_set(x_3112, 1, x_3111);
x_3113 = lean_array_push(x_3095, x_3112);
lean_inc(x_14);
x_3114 = lean_array_push(x_3095, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3115 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3115 = lean_box(0);
}
if (lean_is_scalar(x_3115)) {
 x_3116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3116 = x_3115;
}
lean_ctor_set(x_3116, 0, x_3104);
lean_ctor_set(x_3116, 1, x_3114);
x_3117 = lean_array_push(x_3113, x_3116);
x_3118 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3119, 0, x_3090);
lean_ctor_set(x_3119, 1, x_3118);
x_3120 = lean_array_push(x_3117, x_3119);
x_3121 = lean_array_push(x_3120, x_3088);
x_3122 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3123, 0, x_3122);
lean_ctor_set(x_3123, 1, x_3121);
x_3124 = lean_array_push(x_3095, x_3123);
x_3125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3125, 0, x_3104);
lean_ctor_set(x_3125, 1, x_3124);
x_3126 = lean_array_push(x_3095, x_3125);
x_3127 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3128, 0, x_3127);
lean_ctor_set(x_3128, 1, x_3126);
x_3129 = lean_array_push(x_3110, x_3128);
x_3130 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3131, 0, x_3130);
lean_ctor_set(x_3131, 1, x_3129);
x_3132 = 1;
x_3133 = lean_box(x_3132);
x_3134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3134, 0, x_3131);
lean_ctor_set(x_3134, 1, x_3133);
lean_ctor_set(x_2973, 1, x_3134);
if (lean_is_scalar(x_3092)) {
 x_3135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3135 = x_3092;
}
lean_ctor_set(x_3135, 0, x_2973);
lean_ctor_set(x_3135, 1, x_3091);
return x_3135;
}
}
else
{
lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; uint8_t x_3182; lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; 
x_3136 = lean_ctor_get(x_2973, 0);
lean_inc(x_3136);
lean_dec(x_2973);
x_3137 = lean_ctor_get(x_2974, 0);
lean_inc(x_3137);
if (lean_is_exclusive(x_2974)) {
 lean_ctor_release(x_2974, 0);
 lean_ctor_release(x_2974, 1);
 x_3138 = x_2974;
} else {
 lean_dec_ref(x_2974);
 x_3138 = lean_box(0);
}
x_3139 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_2975);
lean_dec(x_5);
x_3140 = lean_ctor_get(x_3139, 0);
lean_inc(x_3140);
x_3141 = lean_ctor_get(x_3139, 1);
lean_inc(x_3141);
if (lean_is_exclusive(x_3139)) {
 lean_ctor_release(x_3139, 0);
 lean_ctor_release(x_3139, 1);
 x_3142 = x_3139;
} else {
 lean_dec_ref(x_3139);
 x_3142 = lean_box(0);
}
x_3143 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3140);
x_3144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3144, 0, x_3140);
lean_ctor_set(x_3144, 1, x_3143);
x_3145 = l_Array_empty___closed__1;
x_3146 = lean_array_push(x_3145, x_3144);
x_3147 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3148 = lean_array_push(x_3146, x_3147);
x_3149 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3150 = lean_array_push(x_3149, x_2965);
x_3151 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3152, 0, x_3151);
lean_ctor_set(x_3152, 1, x_3150);
x_3153 = lean_array_push(x_3145, x_3152);
x_3154 = l_Lean_nullKind___closed__2;
x_3155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3155, 0, x_3154);
lean_ctor_set(x_3155, 1, x_3153);
x_3156 = lean_array_push(x_3148, x_3155);
x_3157 = lean_array_push(x_3156, x_3147);
x_3158 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3140);
x_3159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3159, 0, x_3140);
lean_ctor_set(x_3159, 1, x_3158);
x_3160 = lean_array_push(x_3157, x_3159);
x_3161 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3140);
x_3162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3162, 0, x_3140);
lean_ctor_set(x_3162, 1, x_3161);
x_3163 = lean_array_push(x_3145, x_3162);
lean_inc(x_14);
x_3164 = lean_array_push(x_3145, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3165 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3165 = lean_box(0);
}
if (lean_is_scalar(x_3165)) {
 x_3166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3166 = x_3165;
}
lean_ctor_set(x_3166, 0, x_3154);
lean_ctor_set(x_3166, 1, x_3164);
x_3167 = lean_array_push(x_3163, x_3166);
x_3168 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3169, 0, x_3140);
lean_ctor_set(x_3169, 1, x_3168);
x_3170 = lean_array_push(x_3167, x_3169);
x_3171 = lean_array_push(x_3170, x_3137);
x_3172 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3173, 0, x_3172);
lean_ctor_set(x_3173, 1, x_3171);
x_3174 = lean_array_push(x_3145, x_3173);
x_3175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3175, 0, x_3154);
lean_ctor_set(x_3175, 1, x_3174);
x_3176 = lean_array_push(x_3145, x_3175);
x_3177 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3178, 0, x_3177);
lean_ctor_set(x_3178, 1, x_3176);
x_3179 = lean_array_push(x_3160, x_3178);
x_3180 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3181, 0, x_3180);
lean_ctor_set(x_3181, 1, x_3179);
x_3182 = 1;
x_3183 = lean_box(x_3182);
if (lean_is_scalar(x_3138)) {
 x_3184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3184 = x_3138;
}
lean_ctor_set(x_3184, 0, x_3181);
lean_ctor_set(x_3184, 1, x_3183);
x_3185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3185, 0, x_3136);
lean_ctor_set(x_3185, 1, x_3184);
if (lean_is_scalar(x_3142)) {
 x_3186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3186 = x_3142;
}
lean_ctor_set(x_3186, 0, x_3185);
lean_ctor_set(x_3186, 1, x_3141);
return x_3186;
}
}
}
case 2:
{
lean_object* x_3187; lean_object* x_3188; lean_object* x_3189; lean_object* x_3190; lean_object* x_3191; lean_object* x_3192; lean_object* x_3193; lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; uint8_t x_3199; 
lean_inc(x_5);
x_3187 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_3188 = lean_ctor_get(x_3187, 0);
lean_inc(x_3188);
x_3189 = lean_ctor_get(x_3187, 1);
lean_inc(x_3189);
lean_dec(x_3187);
x_3190 = lean_unsigned_to_nat(1u);
x_3191 = lean_nat_add(x_3, x_3190);
lean_dec(x_3);
x_3192 = l_Lean_mkHole(x_14);
lean_inc(x_3188);
x_3193 = l_Lean_Elab_Term_mkExplicitBinder(x_3188, x_3192);
x_3194 = lean_array_push(x_4, x_3193);
lean_inc(x_5);
x_3195 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3191, x_3194, x_5, x_3189);
x_3196 = lean_ctor_get(x_3195, 0);
lean_inc(x_3196);
x_3197 = lean_ctor_get(x_3196, 1);
lean_inc(x_3197);
x_3198 = lean_ctor_get(x_3195, 1);
lean_inc(x_3198);
lean_dec(x_3195);
x_3199 = !lean_is_exclusive(x_3196);
if (x_3199 == 0)
{
lean_object* x_3200; uint8_t x_3201; 
x_3200 = lean_ctor_get(x_3196, 1);
lean_dec(x_3200);
x_3201 = !lean_is_exclusive(x_3197);
if (x_3201 == 0)
{
lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; uint8_t x_3205; 
x_3202 = lean_ctor_get(x_3197, 0);
x_3203 = lean_ctor_get(x_3197, 1);
lean_dec(x_3203);
x_3204 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_3198);
lean_dec(x_5);
x_3205 = !lean_is_exclusive(x_3204);
if (x_3205 == 0)
{
lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; uint8_t x_3229; 
x_3206 = lean_ctor_get(x_3204, 0);
x_3207 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3206);
x_3208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3208, 0, x_3206);
lean_ctor_set(x_3208, 1, x_3207);
x_3209 = l_Array_empty___closed__1;
x_3210 = lean_array_push(x_3209, x_3208);
x_3211 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3212 = lean_array_push(x_3210, x_3211);
x_3213 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3214 = lean_array_push(x_3213, x_3188);
x_3215 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3216, 0, x_3215);
lean_ctor_set(x_3216, 1, x_3214);
x_3217 = lean_array_push(x_3209, x_3216);
x_3218 = l_Lean_nullKind___closed__2;
x_3219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3219, 0, x_3218);
lean_ctor_set(x_3219, 1, x_3217);
x_3220 = lean_array_push(x_3212, x_3219);
x_3221 = lean_array_push(x_3220, x_3211);
x_3222 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3206);
x_3223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3223, 0, x_3206);
lean_ctor_set(x_3223, 1, x_3222);
x_3224 = lean_array_push(x_3221, x_3223);
x_3225 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3206);
x_3226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3226, 0, x_3206);
lean_ctor_set(x_3226, 1, x_3225);
x_3227 = lean_array_push(x_3209, x_3226);
lean_inc(x_14);
x_3228 = lean_array_push(x_3209, x_14);
x_3229 = !lean_is_exclusive(x_14);
if (x_3229 == 0)
{
lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; lean_object* x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; lean_object* x_3246; uint8_t x_3247; lean_object* x_3248; 
x_3230 = lean_ctor_get(x_14, 1);
lean_dec(x_3230);
x_3231 = lean_ctor_get(x_14, 0);
lean_dec(x_3231);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_3228);
lean_ctor_set(x_14, 0, x_3218);
x_3232 = lean_array_push(x_3227, x_14);
x_3233 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3234, 0, x_3206);
lean_ctor_set(x_3234, 1, x_3233);
x_3235 = lean_array_push(x_3232, x_3234);
x_3236 = lean_array_push(x_3235, x_3202);
x_3237 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3238, 0, x_3237);
lean_ctor_set(x_3238, 1, x_3236);
x_3239 = lean_array_push(x_3209, x_3238);
x_3240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3240, 0, x_3218);
lean_ctor_set(x_3240, 1, x_3239);
x_3241 = lean_array_push(x_3209, x_3240);
x_3242 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3243, 0, x_3242);
lean_ctor_set(x_3243, 1, x_3241);
x_3244 = lean_array_push(x_3224, x_3243);
x_3245 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3246, 0, x_3245);
lean_ctor_set(x_3246, 1, x_3244);
x_3247 = 1;
x_3248 = lean_box(x_3247);
lean_ctor_set(x_3197, 1, x_3248);
lean_ctor_set(x_3197, 0, x_3246);
lean_ctor_set(x_3204, 0, x_3196);
return x_3204;
}
else
{
lean_object* x_3249; lean_object* x_3250; lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; uint8_t x_3265; lean_object* x_3266; 
lean_dec(x_14);
x_3249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3249, 0, x_3218);
lean_ctor_set(x_3249, 1, x_3228);
x_3250 = lean_array_push(x_3227, x_3249);
x_3251 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3252, 0, x_3206);
lean_ctor_set(x_3252, 1, x_3251);
x_3253 = lean_array_push(x_3250, x_3252);
x_3254 = lean_array_push(x_3253, x_3202);
x_3255 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3256, 0, x_3255);
lean_ctor_set(x_3256, 1, x_3254);
x_3257 = lean_array_push(x_3209, x_3256);
x_3258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3258, 0, x_3218);
lean_ctor_set(x_3258, 1, x_3257);
x_3259 = lean_array_push(x_3209, x_3258);
x_3260 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3261, 0, x_3260);
lean_ctor_set(x_3261, 1, x_3259);
x_3262 = lean_array_push(x_3224, x_3261);
x_3263 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3264, 0, x_3263);
lean_ctor_set(x_3264, 1, x_3262);
x_3265 = 1;
x_3266 = lean_box(x_3265);
lean_ctor_set(x_3197, 1, x_3266);
lean_ctor_set(x_3197, 0, x_3264);
lean_ctor_set(x_3204, 0, x_3196);
return x_3204;
}
}
else
{
lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; lean_object* x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; lean_object* x_3306; lean_object* x_3307; uint8_t x_3308; lean_object* x_3309; lean_object* x_3310; 
x_3267 = lean_ctor_get(x_3204, 0);
x_3268 = lean_ctor_get(x_3204, 1);
lean_inc(x_3268);
lean_inc(x_3267);
lean_dec(x_3204);
x_3269 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3267);
x_3270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3270, 0, x_3267);
lean_ctor_set(x_3270, 1, x_3269);
x_3271 = l_Array_empty___closed__1;
x_3272 = lean_array_push(x_3271, x_3270);
x_3273 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3274 = lean_array_push(x_3272, x_3273);
x_3275 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3276 = lean_array_push(x_3275, x_3188);
x_3277 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3278, 0, x_3277);
lean_ctor_set(x_3278, 1, x_3276);
x_3279 = lean_array_push(x_3271, x_3278);
x_3280 = l_Lean_nullKind___closed__2;
x_3281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3281, 0, x_3280);
lean_ctor_set(x_3281, 1, x_3279);
x_3282 = lean_array_push(x_3274, x_3281);
x_3283 = lean_array_push(x_3282, x_3273);
x_3284 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3267);
x_3285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3285, 0, x_3267);
lean_ctor_set(x_3285, 1, x_3284);
x_3286 = lean_array_push(x_3283, x_3285);
x_3287 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3267);
x_3288 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3288, 0, x_3267);
lean_ctor_set(x_3288, 1, x_3287);
x_3289 = lean_array_push(x_3271, x_3288);
lean_inc(x_14);
x_3290 = lean_array_push(x_3271, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3291 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3291 = lean_box(0);
}
if (lean_is_scalar(x_3291)) {
 x_3292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3292 = x_3291;
 lean_ctor_set_tag(x_3292, 1);
}
lean_ctor_set(x_3292, 0, x_3280);
lean_ctor_set(x_3292, 1, x_3290);
x_3293 = lean_array_push(x_3289, x_3292);
x_3294 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3295 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3295, 0, x_3267);
lean_ctor_set(x_3295, 1, x_3294);
x_3296 = lean_array_push(x_3293, x_3295);
x_3297 = lean_array_push(x_3296, x_3202);
x_3298 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3299, 0, x_3298);
lean_ctor_set(x_3299, 1, x_3297);
x_3300 = lean_array_push(x_3271, x_3299);
x_3301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3301, 0, x_3280);
lean_ctor_set(x_3301, 1, x_3300);
x_3302 = lean_array_push(x_3271, x_3301);
x_3303 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3304, 0, x_3303);
lean_ctor_set(x_3304, 1, x_3302);
x_3305 = lean_array_push(x_3286, x_3304);
x_3306 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3307, 0, x_3306);
lean_ctor_set(x_3307, 1, x_3305);
x_3308 = 1;
x_3309 = lean_box(x_3308);
lean_ctor_set(x_3197, 1, x_3309);
lean_ctor_set(x_3197, 0, x_3307);
x_3310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3310, 0, x_3196);
lean_ctor_set(x_3310, 1, x_3268);
return x_3310;
}
}
else
{
lean_object* x_3311; lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; lean_object* x_3315; lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; uint8_t x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; 
x_3311 = lean_ctor_get(x_3197, 0);
lean_inc(x_3311);
lean_dec(x_3197);
x_3312 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_3198);
lean_dec(x_5);
x_3313 = lean_ctor_get(x_3312, 0);
lean_inc(x_3313);
x_3314 = lean_ctor_get(x_3312, 1);
lean_inc(x_3314);
if (lean_is_exclusive(x_3312)) {
 lean_ctor_release(x_3312, 0);
 lean_ctor_release(x_3312, 1);
 x_3315 = x_3312;
} else {
 lean_dec_ref(x_3312);
 x_3315 = lean_box(0);
}
x_3316 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3313);
x_3317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3317, 0, x_3313);
lean_ctor_set(x_3317, 1, x_3316);
x_3318 = l_Array_empty___closed__1;
x_3319 = lean_array_push(x_3318, x_3317);
x_3320 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3321 = lean_array_push(x_3319, x_3320);
x_3322 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3323 = lean_array_push(x_3322, x_3188);
x_3324 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3325, 0, x_3324);
lean_ctor_set(x_3325, 1, x_3323);
x_3326 = lean_array_push(x_3318, x_3325);
x_3327 = l_Lean_nullKind___closed__2;
x_3328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3328, 0, x_3327);
lean_ctor_set(x_3328, 1, x_3326);
x_3329 = lean_array_push(x_3321, x_3328);
x_3330 = lean_array_push(x_3329, x_3320);
x_3331 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3313);
x_3332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3332, 0, x_3313);
lean_ctor_set(x_3332, 1, x_3331);
x_3333 = lean_array_push(x_3330, x_3332);
x_3334 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3313);
x_3335 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3335, 0, x_3313);
lean_ctor_set(x_3335, 1, x_3334);
x_3336 = lean_array_push(x_3318, x_3335);
lean_inc(x_14);
x_3337 = lean_array_push(x_3318, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3338 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3338 = lean_box(0);
}
if (lean_is_scalar(x_3338)) {
 x_3339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3339 = x_3338;
 lean_ctor_set_tag(x_3339, 1);
}
lean_ctor_set(x_3339, 0, x_3327);
lean_ctor_set(x_3339, 1, x_3337);
x_3340 = lean_array_push(x_3336, x_3339);
x_3341 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3342, 0, x_3313);
lean_ctor_set(x_3342, 1, x_3341);
x_3343 = lean_array_push(x_3340, x_3342);
x_3344 = lean_array_push(x_3343, x_3311);
x_3345 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3346, 0, x_3345);
lean_ctor_set(x_3346, 1, x_3344);
x_3347 = lean_array_push(x_3318, x_3346);
x_3348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3348, 0, x_3327);
lean_ctor_set(x_3348, 1, x_3347);
x_3349 = lean_array_push(x_3318, x_3348);
x_3350 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3351, 0, x_3350);
lean_ctor_set(x_3351, 1, x_3349);
x_3352 = lean_array_push(x_3333, x_3351);
x_3353 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3354, 0, x_3353);
lean_ctor_set(x_3354, 1, x_3352);
x_3355 = 1;
x_3356 = lean_box(x_3355);
x_3357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3357, 0, x_3354);
lean_ctor_set(x_3357, 1, x_3356);
lean_ctor_set(x_3196, 1, x_3357);
if (lean_is_scalar(x_3315)) {
 x_3358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3358 = x_3315;
}
lean_ctor_set(x_3358, 0, x_3196);
lean_ctor_set(x_3358, 1, x_3314);
return x_3358;
}
}
else
{
lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; lean_object* x_3366; lean_object* x_3367; lean_object* x_3368; lean_object* x_3369; lean_object* x_3370; lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; lean_object* x_3375; lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; lean_object* x_3385; lean_object* x_3386; lean_object* x_3387; lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; uint8_t x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; 
x_3359 = lean_ctor_get(x_3196, 0);
lean_inc(x_3359);
lean_dec(x_3196);
x_3360 = lean_ctor_get(x_3197, 0);
lean_inc(x_3360);
if (lean_is_exclusive(x_3197)) {
 lean_ctor_release(x_3197, 0);
 lean_ctor_release(x_3197, 1);
 x_3361 = x_3197;
} else {
 lean_dec_ref(x_3197);
 x_3361 = lean_box(0);
}
x_3362 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_3198);
lean_dec(x_5);
x_3363 = lean_ctor_get(x_3362, 0);
lean_inc(x_3363);
x_3364 = lean_ctor_get(x_3362, 1);
lean_inc(x_3364);
if (lean_is_exclusive(x_3362)) {
 lean_ctor_release(x_3362, 0);
 lean_ctor_release(x_3362, 1);
 x_3365 = x_3362;
} else {
 lean_dec_ref(x_3362);
 x_3365 = lean_box(0);
}
x_3366 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_3363);
x_3367 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3367, 0, x_3363);
lean_ctor_set(x_3367, 1, x_3366);
x_3368 = l_Array_empty___closed__1;
x_3369 = lean_array_push(x_3368, x_3367);
x_3370 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_3371 = lean_array_push(x_3369, x_3370);
x_3372 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_3373 = lean_array_push(x_3372, x_3188);
x_3374 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_3375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3375, 0, x_3374);
lean_ctor_set(x_3375, 1, x_3373);
x_3376 = lean_array_push(x_3368, x_3375);
x_3377 = l_Lean_nullKind___closed__2;
x_3378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3378, 0, x_3377);
lean_ctor_set(x_3378, 1, x_3376);
x_3379 = lean_array_push(x_3371, x_3378);
x_3380 = lean_array_push(x_3379, x_3370);
x_3381 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_3363);
x_3382 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3382, 0, x_3363);
lean_ctor_set(x_3382, 1, x_3381);
x_3383 = lean_array_push(x_3380, x_3382);
x_3384 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_3363);
x_3385 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3385, 0, x_3363);
lean_ctor_set(x_3385, 1, x_3384);
x_3386 = lean_array_push(x_3368, x_3385);
lean_inc(x_14);
x_3387 = lean_array_push(x_3368, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3388 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3388 = lean_box(0);
}
if (lean_is_scalar(x_3388)) {
 x_3389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3389 = x_3388;
 lean_ctor_set_tag(x_3389, 1);
}
lean_ctor_set(x_3389, 0, x_3377);
lean_ctor_set(x_3389, 1, x_3387);
x_3390 = lean_array_push(x_3386, x_3389);
x_3391 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_3392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3392, 0, x_3363);
lean_ctor_set(x_3392, 1, x_3391);
x_3393 = lean_array_push(x_3390, x_3392);
x_3394 = lean_array_push(x_3393, x_3360);
x_3395 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_3396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3396, 0, x_3395);
lean_ctor_set(x_3396, 1, x_3394);
x_3397 = lean_array_push(x_3368, x_3396);
x_3398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3398, 0, x_3377);
lean_ctor_set(x_3398, 1, x_3397);
x_3399 = lean_array_push(x_3368, x_3398);
x_3400 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_3401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3401, 0, x_3400);
lean_ctor_set(x_3401, 1, x_3399);
x_3402 = lean_array_push(x_3383, x_3401);
x_3403 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_3404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3404, 0, x_3403);
lean_ctor_set(x_3404, 1, x_3402);
x_3405 = 1;
x_3406 = lean_box(x_3405);
if (lean_is_scalar(x_3361)) {
 x_3407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3407 = x_3361;
}
lean_ctor_set(x_3407, 0, x_3404);
lean_ctor_set(x_3407, 1, x_3406);
x_3408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3408, 0, x_3359);
lean_ctor_set(x_3408, 1, x_3407);
if (lean_is_scalar(x_3365)) {
 x_3409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3409 = x_3365;
}
lean_ctor_set(x_3409, 0, x_3408);
lean_ctor_set(x_3409, 1, x_3364);
return x_3409;
}
}
default: 
{
lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; 
x_3410 = l_Lean_mkHole(x_14);
x_3411 = lean_unsigned_to_nat(1u);
x_3412 = lean_nat_add(x_3, x_3411);
lean_dec(x_3);
x_3413 = l_Lean_Elab_Term_mkExplicitBinder(x_14, x_3410);
x_3414 = lean_array_push(x_4, x_3413);
x_3 = x_3412;
x_4 = x_3414;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandFunBinders(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_FunBinders_State_fvars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_whnfForall(x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 7)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Meta_isExprDefEq(x_2, x_23, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_expr_instantiate1(x_24, x_1);
lean_dec(x_24);
lean_ctor_set(x_11, 0, x_28);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_expr_instantiate1(x_24, x_1);
lean_dec(x_24);
lean_ctor_set(x_11, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_free_object(x_11);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_20, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_3, 3, x_38);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_box(0);
lean_ctor_set(x_3, 3, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_11);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Meta_whnfForall(x_46, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 7)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 2);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_Meta_isExprDefEq(x_2, x_50, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
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
x_55 = lean_expr_instantiate1(x_51, x_1);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_3, 3, x_56);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
lean_ctor_set(x_3, 3, x_64);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_66 = lean_ctor_get(x_47, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_47, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_68 = x_47;
} else {
 lean_dec_ref(x_47);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_3, 0);
x_71 = lean_ctor_get(x_3, 1);
x_72 = lean_ctor_get(x_3, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_3);
x_73 = lean_ctor_get(x_11, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_74 = x_11;
} else {
 lean_dec_ref(x_11);
 x_74 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_75 = l_Lean_Meta_whnfForall(x_73, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 7)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 2);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Lean_Meta_isExprDefEq(x_2, x_78, x_6, x_7, x_8, x_9, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
x_83 = lean_expr_instantiate1(x_79, x_1);
lean_dec(x_79);
if (lean_is_scalar(x_74)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_74;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_85, 1, x_71);
lean_ctor_set(x_85, 2, x_72);
lean_ctor_set(x_85, 3, x_84);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_89 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_92 = x_75;
} else {
 lean_dec_ref(x_75);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_70);
lean_ctor_set(x_94, 1, x_71);
lean_ctor_set(x_94, 2, x_72);
lean_ctor_set(x_94, 3, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_96 = lean_ctor_get(x_75, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_98 = x_75;
} else {
 lean_dec_ref(x_75);
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg___boxed), 2, 0);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_8, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(x_14, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l_Lean_mkFVar(x_19);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_inc(x_21);
x_23 = lean_array_push(x_22, x_21);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_3);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = l_Lean_Syntax_getId(x_26);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
lean_inc(x_8);
x_29 = lean_local_ctx_mk_local_decl(x_3, x_19, x_27, x_8, x_28);
lean_inc(x_21);
lean_inc(x_26);
lean_inc(x_29);
x_30 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore(x_29, x_26, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_13, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_13, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_13, 7);
lean_inc(x_39);
x_40 = l_Lean_replaceRef(x_26, x_35);
lean_dec(x_35);
lean_dec(x_26);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_36);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_41, 6, x_38);
lean_ctor_set(x_41, 7, x_39);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
x_42 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(x_21, x_8, x_25, x_9, x_10, x_11, x_12, x_41, x_14, x_31);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 2);
x_48 = lean_ctor_get(x_43, 3);
x_49 = lean_ctor_get(x_43, 1);
lean_dec(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_29);
lean_inc(x_46);
lean_ctor_set(x_43, 1, x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_50 = l_Lean_Meta_isClass_x3f(x_8, x_11, x_12, x_13, x_14, x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_29);
lean_dec(x_21);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_6, x_53);
x_55 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_54, x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_43);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_21);
x_59 = lean_array_push(x_47, x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_6, x_60);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_29);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_48);
x_63 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_56);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_66 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_61, x_62, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_restoreSynthInstanceCache(x_64, x_11, x_12, x_13, x_14, x_68);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_dec(x_66);
x_76 = l_Lean_Meta_restoreSynthInstanceCache(x_64, x_11, x_12, x_13, x_14, x_75);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_43);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_81 = !lean_is_exclusive(x_50);
if (x_81 == 0)
{
return x_50;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_50, 0);
x_83 = lean_ctor_get(x_50, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_50);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_43, 0);
x_86 = lean_ctor_get(x_43, 2);
x_87 = lean_ctor_get(x_43, 3);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_43);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_29);
lean_inc(x_85);
x_88 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_29);
lean_ctor_set(x_88, 2, x_86);
lean_ctor_set(x_88, 3, x_87);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_89 = l_Lean_Meta_isClass_x3f(x_8, x_11, x_12, x_13, x_14, x_44);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_29);
lean_dec(x_21);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_6, x_92);
x_94 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_93, x_88, x_9, x_10, x_11, x_12, x_13, x_14, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_88);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
lean_dec(x_90);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_21);
x_98 = lean_array_push(x_86, x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_6, x_99);
x_101 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_29);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_87);
x_102 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_95);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_105 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_100, x_101, x_9, x_10, x_11, x_12, x_13, x_14, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_restoreSynthInstanceCache(x_103, x_11, x_12, x_13, x_14, x_107);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
lean_dec(x_105);
x_114 = l_Lean_Meta_restoreSynthInstanceCache(x_103, x_11, x_12, x_13, x_14, x_113);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
 lean_ctor_set_tag(x_117, 1);
}
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_118 = lean_ctor_get(x_89, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_89, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_120 = x_89;
} else {
 lean_dec_ref(x_89);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_122 = !lean_is_exclusive(x_42);
if (x_122 == 0)
{
return x_42;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_42, 0);
x_124 = lean_ctor_get(x_42, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_42);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_4);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType), 8, 1);
lean_closure_set(x_20, 0, x_17);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1___boxed), 15, 7);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_14);
lean_closure_set(x_21, 5, x_2);
lean_closure_set(x_21, 6, x_1);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 3);
x_25 = l_Lean_replaceRef(x_17, x_24);
lean_dec(x_24);
lean_dec(x_17);
lean_ctor_set(x_8, 3, x_25);
x_26 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_18, x_19, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 2);
x_30 = lean_ctor_get(x_8, 3);
x_31 = lean_ctor_get(x_8, 4);
x_32 = lean_ctor_get(x_8, 5);
x_33 = lean_ctor_get(x_8, 6);
x_34 = lean_ctor_get(x_8, 7);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_35 = l_Lean_replaceRef(x_17, x_30);
lean_dec(x_30);
lean_dec(x_17);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_31);
lean_ctor_set(x_36, 5, x_32);
lean_ctor_set(x_36, 6, x_33);
lean_ctor_set(x_36, 7, x_34);
x_37 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_18, x_19, x_22, x_4, x_5, x_6, x_7, x_36, x_9, x_16);
return x_37;
}
}
else
{
uint8_t x_38; 
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
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_20;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_empty___closed__1;
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_2);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_18, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_14);
lean_dec(x_14);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 3);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_apply_2(x_3, x_27, x_28);
if (x_25 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_26, x_23, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_7, x_8, x_9, x_21);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_34 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_26, x_23, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_restoreSynthInstanceCache(x_32, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_44 = l_Lean_Meta_restoreSynthInstanceCache(x_32, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_53; lean_object* x_54; 
x_53 = l_Array_empty___closed__1;
x_54 = lean_apply_9(x_3, x_53, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_54;
}
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFunBinders___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabFunBinders___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Syntax_getSepArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_groupKind___closed__2;
lean_inc(x_2);
x_4 = l_Lean_Syntax_isOfKind(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Parser_Term_letRecDecl___elambda__1___closed__1;
x_9 = lean_name_mk_string(x_1, x_8);
lean_inc(x_7);
x_10 = l_Lean_Syntax_isOfKind(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
lean_dec(x_2);
x_14 = l_Lean_Syntax_isNone(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Syntax_isNodeOf(x_13, x_15, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandWhereDecls___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Term_whereDecls_formatter___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_expandWhereDecls___closed__1;
x_13 = l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_5248____spec__1(x_11, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_3, x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_myMacro____x40_Init_Notation___hyg_16821____closed__1;
lean_inc(x_19);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__3;
lean_inc(x_19);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_23, x_25);
x_27 = l_Lean_groupKind___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_22, x_28);
x_30 = l_myMacro____x40_Init_Notation___hyg_1346____closed__7;
x_31 = l_Lean_Syntax_SepArray_ofElems(x_30, x_16);
lean_dec(x_16);
x_32 = l_Array_appendCore___rarg(x_22, x_31);
lean_dec(x_31);
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_22, x_34);
x_36 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__1;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_29, x_37);
x_39 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_push(x_22, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_38, x_42);
x_44 = lean_array_push(x_43, x_2);
x_45 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_17, 0, x_46);
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = l_myMacro____x40_Init_Notation___hyg_16821____closed__1;
lean_inc(x_47);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Array_empty___closed__1;
x_52 = lean_array_push(x_51, x_50);
x_53 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__3;
lean_inc(x_47);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_52, x_54);
x_56 = l_Lean_groupKind___closed__2;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_51, x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_1346____closed__7;
x_60 = l_Lean_Syntax_SepArray_ofElems(x_59, x_16);
lean_dec(x_16);
x_61 = l_Array_appendCore___rarg(x_51, x_60);
lean_dec(x_60);
x_62 = l_Lean_nullKind___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_51, x_63);
x_65 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__1;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_array_push(x_58, x_66);
x_68 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_47);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_51, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_67, x_71);
x_73 = lean_array_push(x_72, x_2);
x_74 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_21281____closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_48);
return x_76;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandWhereDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isNone(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Elab_Term_expandWhereDecls(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_6;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = l_myMacro____x40_Init_Notation___hyg_15342____closed__3;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_array_push(x_2, x_3);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = 1;
x_19 = x_5 + x_18;
x_20 = x_17;
x_21 = lean_array_uset(x_11, x_5, x_20);
x_5 = x_19;
x_6 = x_21;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_6;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
x_15 = l_myMacro____x40_Init_Notation___hyg_15342____closed__3;
x_16 = lean_name_mk_string(x_14, x_15);
lean_inc(x_3);
lean_inc(x_2);
x_17 = lean_array_push(x_2, x_3);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = x_5 + x_20;
x_22 = x_19;
x_23 = lean_array_uset(x_11, x_5, x_22);
x_5 = x_21;
x_6 = x_23;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkArrow___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_mkArrow___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_nat_add(x_12, x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_15);
lean_ctor_set(x_5, 2, x_12);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkArrow___closed__2;
x_21 = l_Lean_addMacroScope(x_15, x_20, x_12);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Array_empty___closed__1;
x_31 = lean_array_push(x_30, x_29);
lean_inc(x_24);
x_32 = lean_array_push(x_31, x_24);
x_33 = l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_4, x_34);
lean_inc(x_5);
x_36 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_35, x_5, x_27);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_38);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
x_43 = lean_array_push(x_30, x_42);
x_44 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_41);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_30, x_45);
x_47 = lean_array_push(x_30, x_24);
x_48 = l_Lean_nullKind___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_30, x_49);
x_51 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_50, x_52);
x_54 = lean_array_push(x_53, x_37);
x_55 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_push(x_46, x_56);
x_58 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_array_push(x_43, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_33);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_39, 0, x_61);
return x_39;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_62 = lean_ctor_get(x_39, 0);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_39);
lean_inc(x_62);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_28);
x_65 = lean_array_push(x_30, x_64);
x_66 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_62);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_30, x_67);
x_69 = lean_array_push(x_30, x_24);
x_70 = l_Lean_nullKind___closed__2;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_push(x_30, x_71);
x_73 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_72, x_74);
x_76 = lean_array_push(x_75, x_37);
x_77 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_array_push(x_68, x_78);
x_80 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_65, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_33);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_63);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_36, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_36, 1);
lean_inc(x_86);
lean_dec(x_36);
x_87 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_86);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_89);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_array_push(x_30, x_91);
x_93 = lean_array_push(x_30, x_24);
x_94 = l_Lean_nullKind___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_array_push(x_92, x_95);
x_97 = l_Lean_Parser_Tactic_intro___closed__4;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_30, x_98);
x_100 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_push(x_99, x_101);
x_103 = lean_array_push(x_102, x_85);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_push(x_30, x_104);
x_106 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
lean_ctor_set(x_87, 0, x_107);
return x_87;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_108 = lean_ctor_get(x_87, 0);
x_109 = lean_ctor_get(x_87, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_87);
x_110 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_108);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_array_push(x_30, x_111);
x_113 = lean_array_push(x_30, x_24);
x_114 = l_Lean_nullKind___closed__2;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_array_push(x_112, x_115);
x_117 = l_Lean_Parser_Tactic_intro___closed__4;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_30, x_118);
x_120 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_108);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_push(x_119, x_121);
x_123 = lean_array_push(x_122, x_85);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_30, x_124);
x_126 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__2;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_109);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_129 = lean_ctor_get(x_5, 0);
x_130 = lean_ctor_get(x_5, 1);
x_131 = lean_ctor_get(x_5, 3);
x_132 = lean_ctor_get(x_5, 4);
x_133 = lean_ctor_get(x_5, 5);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_130);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_12);
lean_ctor_set(x_134, 3, x_131);
lean_ctor_set(x_134, 4, x_132);
lean_ctor_set(x_134, 5, x_133);
x_135 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_134, x_6);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Meta_mkArrow___closed__2;
x_139 = l_Lean_addMacroScope(x_130, x_138, x_12);
x_140 = lean_box(0);
x_141 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_142 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_140);
x_143 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_134, x_137);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Array_empty___closed__1;
x_149 = lean_array_push(x_148, x_147);
lean_inc(x_142);
x_150 = lean_array_push(x_149, x_142);
x_151 = l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_4, x_152);
lean_inc(x_134);
x_154 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_153, x_134, x_145);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_134, x_156);
lean_dec(x_134);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
lean_inc(x_158);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_146);
x_162 = lean_array_push(x_148, x_161);
x_163 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_158);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_148, x_164);
x_166 = lean_array_push(x_148, x_142);
x_167 = l_Lean_nullKind___closed__2;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_push(x_148, x_168);
x_170 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_158);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_array_push(x_169, x_171);
x_173 = lean_array_push(x_172, x_155);
x_174 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_array_push(x_165, x_175);
x_177 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = lean_array_push(x_162, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_151);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_160)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_160;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_159);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_182 = lean_ctor_get(x_154, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_154, 1);
lean_inc(x_183);
lean_dec(x_154);
x_184 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_134, x_183);
lean_dec(x_134);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_185);
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_148, x_189);
x_191 = lean_array_push(x_148, x_142);
x_192 = l_Lean_nullKind___closed__2;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_array_push(x_190, x_193);
x_195 = l_Lean_Parser_Tactic_intro___closed__4;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_array_push(x_148, x_196);
x_198 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_array_push(x_197, x_199);
x_201 = lean_array_push(x_200, x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_array_push(x_148, x_202);
x_204 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__2;
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
if (lean_is_scalar(x_187)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_187;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_186);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_207 = lean_ctor_get(x_6, 0);
x_208 = lean_ctor_get(x_6, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_6);
x_209 = lean_nat_add(x_207, x_9);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_ctor_get(x_5, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_5, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_5, 3);
lean_inc(x_213);
x_214 = lean_ctor_get(x_5, 4);
lean_inc(x_214);
x_215 = lean_ctor_get(x_5, 5);
lean_inc(x_215);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_216 = x_5;
} else {
 lean_dec_ref(x_5);
 x_216 = lean_box(0);
}
lean_inc(x_207);
lean_inc(x_212);
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 6, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_212);
lean_ctor_set(x_217, 2, x_207);
lean_ctor_set(x_217, 3, x_213);
lean_ctor_set(x_217, 4, x_214);
lean_ctor_set(x_217, 5, x_215);
x_218 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_217, x_210);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lean_Meta_mkArrow___closed__2;
x_222 = l_Lean_addMacroScope(x_212, x_221, x_207);
x_223 = lean_box(0);
x_224 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_225 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_225, 0, x_219);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_222);
lean_ctor_set(x_225, 3, x_223);
x_226 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_217, x_220);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Array_empty___closed__1;
x_232 = lean_array_push(x_231, x_230);
lean_inc(x_225);
x_233 = lean_array_push(x_232, x_225);
x_234 = l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = lean_array_push(x_4, x_235);
lean_inc(x_217);
x_237 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_236, x_217, x_228);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_217, x_239);
lean_dec(x_217);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
lean_inc(x_241);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_229);
x_245 = lean_array_push(x_231, x_244);
x_246 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_241);
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_array_push(x_231, x_247);
x_249 = lean_array_push(x_231, x_225);
x_250 = l_Lean_nullKind___closed__2;
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = lean_array_push(x_231, x_251);
x_253 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_254 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_254, 0, x_241);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_array_push(x_252, x_254);
x_256 = lean_array_push(x_255, x_238);
x_257 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
x_259 = lean_array_push(x_248, x_258);
x_260 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = lean_array_push(x_245, x_261);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_234);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_243)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_243;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_242);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_265 = lean_ctor_get(x_237, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_237, 1);
lean_inc(x_266);
lean_dec(x_237);
x_267 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_217, x_266);
lean_dec(x_217);
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
x_271 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_268);
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_268);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_array_push(x_231, x_272);
x_274 = lean_array_push(x_231, x_225);
x_275 = l_Lean_nullKind___closed__2;
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_array_push(x_273, x_276);
x_278 = l_Lean_Parser_Tactic_intro___closed__4;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = lean_array_push(x_231, x_279);
x_281 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
x_282 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_282, 0, x_268);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_array_push(x_280, x_282);
x_284 = lean_array_push(x_283, x_265);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_array_push(x_231, x_285);
x_287 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__2;
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
if (lean_is_scalar(x_270)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_270;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_269);
return x_289;
}
}
}
else
{
if (x_2 == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
lean_dec(x_5);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; size_t x_300; size_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_292 = lean_ctor_get(x_290, 0);
x_293 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_292);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Array_empty___closed__1;
x_296 = lean_array_push(x_295, x_294);
x_297 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_298 = lean_array_push(x_296, x_297);
x_299 = lean_array_get_size(x_4);
x_300 = lean_usize_of_nat(x_299);
lean_dec(x_299);
x_301 = 0;
x_302 = x_4;
x_303 = l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
x_304 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_303, x_295, x_297, x_300, x_301, x_302);
x_305 = x_304;
x_306 = l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
x_307 = l_Lean_mkSepArray(x_305, x_306);
lean_dec(x_305);
x_308 = l_Array_appendCore___rarg(x_295, x_307);
lean_dec(x_307);
x_309 = l_Lean_nullKind___closed__2;
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_308);
x_311 = lean_array_push(x_298, x_310);
x_312 = lean_array_push(x_311, x_297);
x_313 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
x_314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_314, 0, x_292);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_array_push(x_312, x_314);
x_316 = lean_array_push(x_315, x_1);
x_317 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
lean_ctor_set(x_290, 0, x_318);
return x_290;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; size_t x_328; size_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_319 = lean_ctor_get(x_290, 0);
x_320 = lean_ctor_get(x_290, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_290);
x_321 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_319);
x_322 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Array_empty___closed__1;
x_324 = lean_array_push(x_323, x_322);
x_325 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_326 = lean_array_push(x_324, x_325);
x_327 = lean_array_get_size(x_4);
x_328 = lean_usize_of_nat(x_327);
lean_dec(x_327);
x_329 = 0;
x_330 = x_4;
x_331 = l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
x_332 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_331, x_323, x_325, x_328, x_329, x_330);
x_333 = x_332;
x_334 = l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
x_335 = l_Lean_mkSepArray(x_333, x_334);
lean_dec(x_333);
x_336 = l_Array_appendCore___rarg(x_323, x_335);
lean_dec(x_335);
x_337 = l_Lean_nullKind___closed__2;
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_array_push(x_326, x_338);
x_340 = lean_array_push(x_339, x_325);
x_341 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
x_342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_342, 0, x_319);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_array_push(x_340, x_342);
x_344 = lean_array_push(x_343, x_1);
x_345 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_320);
return x_347;
}
}
else
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
lean_dec(x_5);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; size_t x_358; size_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_350 = lean_ctor_get(x_348, 0);
x_351 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_350);
x_352 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Array_empty___closed__1;
x_354 = lean_array_push(x_353, x_352);
x_355 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_356 = lean_array_push(x_354, x_355);
x_357 = lean_array_get_size(x_4);
x_358 = lean_usize_of_nat(x_357);
lean_dec(x_357);
x_359 = 0;
x_360 = x_4;
x_361 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_362 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_361, x_353, x_355, x_358, x_359, x_360);
x_363 = x_362;
x_364 = l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
x_365 = l_Lean_mkSepArray(x_363, x_364);
lean_dec(x_363);
x_366 = l_Array_appendCore___rarg(x_353, x_365);
lean_dec(x_365);
x_367 = l_Lean_nullKind___closed__2;
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = lean_array_push(x_356, x_368);
x_370 = lean_array_push(x_369, x_355);
x_371 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_350);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_array_push(x_370, x_372);
x_374 = lean_array_push(x_373, x_1);
x_375 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
lean_ctor_set(x_348, 0, x_376);
return x_348;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; size_t x_386; size_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_377 = lean_ctor_get(x_348, 0);
x_378 = lean_ctor_get(x_348, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_348);
x_379 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_377);
x_380 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_Array_empty___closed__1;
x_382 = lean_array_push(x_381, x_380);
x_383 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_384 = lean_array_push(x_382, x_383);
x_385 = lean_array_get_size(x_4);
x_386 = lean_usize_of_nat(x_385);
lean_dec(x_385);
x_387 = 0;
x_388 = x_4;
x_389 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_390 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_389, x_381, x_383, x_386, x_387, x_388);
x_391 = x_390;
x_392 = l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
x_393 = l_Lean_mkSepArray(x_391, x_392);
lean_dec(x_391);
x_394 = l_Array_appendCore___rarg(x_381, x_393);
lean_dec(x_393);
x_395 = l_Lean_nullKind___closed__2;
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
x_397 = lean_array_push(x_384, x_396);
x_398 = lean_array_push(x_397, x_383);
x_399 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
x_400 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_400, 0, x_377);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_array_push(x_398, x_400);
x_402 = lean_array_push(x_401, x_1);
x_403 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_378);
return x_405;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 5);
x_9 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_4, 5, x_9);
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_3, x_6, x_10, x_4, x_5);
lean_dec(x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_18);
x_20 = l_Array_empty___closed__1;
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_3, x_6, x_20, x_19, x_5);
lean_dec(x_6);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 5);
x_8 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 5, x_8);
x_9 = 1;
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_9, x_5, x_10, x_3, x_4);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_18);
x_20 = 1;
x_21 = l_Array_empty___closed__1;
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_20, x_5, x_21, x_19, x_4);
lean_dec(x_5);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_6;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = l_myMacro____x40_Init_Notation___hyg_15342____closed__3;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_array_push(x_2, x_3);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = 1;
x_19 = x_5 + x_18;
x_20 = x_17;
x_21 = lean_array_uset(x_11, x_5, x_20);
x_5 = x_19;
x_6 = x_21;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_nat_add(x_12, x_9);
lean_ctor_set(x_6, 0, x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_15);
lean_ctor_set(x_5, 2, x_12);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_Meta_mkArrow___closed__2;
x_25 = l_Lean_addMacroScope(x_15, x_24, x_12);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_25);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_array_push(x_23, x_28);
x_30 = l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_array_push(x_4, x_31);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_32, x_5, x_19);
lean_dec(x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_35);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
x_40 = lean_array_push(x_22, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_38);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_22, x_42);
lean_inc(x_38);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_27);
lean_ctor_set(x_44, 2, x_25);
lean_ctor_set(x_44, 3, x_26);
x_45 = lean_array_push(x_22, x_44);
x_46 = l_Lean_nullKind___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_push(x_22, x_47);
x_49 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_push(x_48, x_50);
x_52 = lean_array_push(x_51, x_34);
x_53 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_array_push(x_43, x_54);
x_56 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_40, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_30);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_36, 0, x_59);
return x_36;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_60 = lean_ctor_get(x_36, 0);
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_36);
lean_inc(x_60);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_20);
x_63 = lean_array_push(x_22, x_62);
x_64 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_60);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_22, x_65);
lean_inc(x_60);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_27);
lean_ctor_set(x_67, 2, x_25);
lean_ctor_set(x_67, 3, x_26);
x_68 = lean_array_push(x_22, x_67);
x_69 = l_Lean_nullKind___closed__2;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_array_push(x_22, x_70);
x_72 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_71, x_73);
x_75 = lean_array_push(x_74, x_34);
x_76 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_66, x_77);
x_79 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_63, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_30);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_61);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_25);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_33);
if (x_84 == 0)
{
return x_33;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_33, 0);
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_33);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
x_90 = lean_ctor_get(x_5, 3);
x_91 = lean_ctor_get(x_5, 4);
x_92 = lean_ctor_get(x_5, 5);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_89);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_12);
lean_ctor_set(x_93, 3, x_90);
lean_ctor_set(x_93, 4, x_91);
lean_ctor_set(x_93, 5, x_92);
x_94 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_93, x_6);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_95);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Array_empty___closed__1;
x_100 = lean_array_push(x_99, x_98);
x_101 = l_Lean_Meta_mkArrow___closed__2;
x_102 = l_Lean_addMacroScope(x_89, x_101, x_12);
x_103 = lean_box(0);
x_104 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_102);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
x_106 = lean_array_push(x_100, x_105);
x_107 = l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_4, x_108);
lean_inc(x_93);
x_110 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_109, x_93, x_96);
lean_dec(x_10);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_93, x_112);
lean_dec(x_93);
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
lean_inc(x_114);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_97);
x_118 = lean_array_push(x_99, x_117);
x_119 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_114);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_99, x_120);
lean_inc(x_114);
x_122 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_104);
lean_ctor_set(x_122, 2, x_102);
lean_ctor_set(x_122, 3, x_103);
x_123 = lean_array_push(x_99, x_122);
x_124 = l_Lean_nullKind___closed__2;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_push(x_99, x_125);
x_127 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_array_push(x_126, x_128);
x_130 = lean_array_push(x_129, x_111);
x_131 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_push(x_121, x_132);
x_134 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_118, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_107);
lean_ctor_set(x_137, 1, x_136);
if (lean_is_scalar(x_116)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_116;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_115);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_102);
lean_dec(x_93);
x_139 = lean_ctor_get(x_110, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_110, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_141 = x_110;
} else {
 lean_dec_ref(x_110);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_143 = lean_ctor_get(x_6, 0);
x_144 = lean_ctor_get(x_6, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_6);
x_145 = lean_nat_add(x_143, x_9);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_ctor_get(x_5, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_5, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_5, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_5, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_5, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_152 = x_5;
} else {
 lean_dec_ref(x_5);
 x_152 = lean_box(0);
}
lean_inc(x_143);
lean_inc(x_148);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 6, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_148);
lean_ctor_set(x_153, 2, x_143);
lean_ctor_set(x_153, 3, x_149);
lean_ctor_set(x_153, 4, x_150);
lean_ctor_set(x_153, 5, x_151);
x_154 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_153, x_146);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_155);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Array_empty___closed__1;
x_160 = lean_array_push(x_159, x_158);
x_161 = l_Lean_Meta_mkArrow___closed__2;
x_162 = l_Lean_addMacroScope(x_148, x_161, x_143);
x_163 = lean_box(0);
x_164 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_162);
x_165 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_162);
lean_ctor_set(x_165, 3, x_163);
x_166 = lean_array_push(x_160, x_165);
x_167 = l_myMacro____x40_Init_NotationExtra___hyg_5711____closed__27;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_push(x_4, x_168);
lean_inc(x_153);
x_170 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_169, x_153, x_156);
lean_dec(x_10);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_153, x_172);
lean_dec(x_153);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
lean_inc(x_174);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_157);
x_178 = lean_array_push(x_159, x_177);
x_179 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_174);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_push(x_159, x_180);
lean_inc(x_174);
x_182 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_182, 0, x_174);
lean_ctor_set(x_182, 1, x_164);
lean_ctor_set(x_182, 2, x_162);
lean_ctor_set(x_182, 3, x_163);
x_183 = lean_array_push(x_159, x_182);
x_184 = l_Lean_nullKind___closed__2;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_push(x_159, x_185);
x_187 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_188 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_188, 0, x_174);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_array_push(x_186, x_188);
x_190 = lean_array_push(x_189, x_171);
x_191 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_181, x_192);
x_194 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_array_push(x_178, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_167);
lean_ctor_set(x_197, 1, x_196);
if (lean_is_scalar(x_176)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_176;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_175);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_162);
lean_dec(x_153);
x_199 = lean_ctor_get(x_170, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_170, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_201 = x_170;
} else {
 lean_dec_ref(x_170);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; uint8_t x_204; 
x_203 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; size_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_205);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Array_empty___closed__1;
x_210 = lean_array_push(x_209, x_208);
x_211 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_212 = lean_array_push(x_210, x_211);
x_213 = lean_array_get_size(x_4);
x_214 = lean_usize_of_nat(x_213);
lean_dec(x_213);
x_215 = 0;
x_216 = x_4;
x_217 = l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
x_218 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_217, x_209, x_211, x_214, x_215, x_216);
x_219 = x_218;
x_220 = l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
x_221 = l_Lean_mkSepArray(x_219, x_220);
lean_dec(x_219);
x_222 = l_Array_appendCore___rarg(x_209, x_221);
lean_dec(x_221);
x_223 = l_Lean_nullKind___closed__2;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_array_push(x_212, x_224);
x_226 = lean_array_push(x_225, x_211);
x_227 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_205);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_array_push(x_226, x_228);
x_230 = lean_array_push(x_229, x_1);
x_231 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l_Lean_Syntax_isNone(x_2);
if (x_233 == 0)
{
lean_object* x_234; 
lean_free_object(x_203);
x_234 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_232, x_5, x_206);
lean_dec(x_5);
return x_234;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_203, 0, x_232);
return x_203;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; size_t x_244; size_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_235 = lean_ctor_get(x_203, 0);
x_236 = lean_ctor_get(x_203, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_203);
x_237 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_235);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Array_empty___closed__1;
x_240 = lean_array_push(x_239, x_238);
x_241 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_242 = lean_array_push(x_240, x_241);
x_243 = lean_array_get_size(x_4);
x_244 = lean_usize_of_nat(x_243);
lean_dec(x_243);
x_245 = 0;
x_246 = x_4;
x_247 = l_myMacro____x40_Init_Notation___hyg_2278____closed__2;
x_248 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_247, x_239, x_241, x_244, x_245, x_246);
x_249 = x_248;
x_250 = l_myMacro____x40_Init_NotationExtra___hyg_5248____closed__6;
x_251 = l_Lean_mkSepArray(x_249, x_250);
lean_dec(x_249);
x_252 = l_Array_appendCore___rarg(x_239, x_251);
lean_dec(x_251);
x_253 = l_Lean_nullKind___closed__2;
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = lean_array_push(x_242, x_254);
x_256 = lean_array_push(x_255, x_241);
x_257 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_235);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_array_push(x_256, x_258);
x_260 = lean_array_push(x_259, x_1);
x_261 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l_Lean_Syntax_isNone(x_2);
if (x_263 == 0)
{
lean_object* x_264; 
x_264 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_262, x_5, x_236);
lean_dec(x_5);
return x_264;
}
else
{
lean_object* x_265; 
lean_dec(x_5);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_236);
return x_265;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(x_5);
x_9 = l_Array_empty___closed__1;
x_10 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_5, x_7, x_8, x_9, x_2, x_3);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAltsWhereDecls(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_expandFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
lean_inc(x_9);
x_13 = l_Lean_Syntax_isOfKind(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_9, x_16, x_2, x_3);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_9, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_9, x_20);
lean_dec(x_9);
x_22 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
lean_inc(x_2);
x_23 = l_Lean_Elab_Term_expandFunBinders(x_22, x_21, x_2, x_3);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = lean_box(1);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_34);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_39);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_empty___closed__1;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Array_appendCore___rarg(x_42, x_35);
lean_dec(x_35);
x_45 = l_Lean_nullKind___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_42, x_46);
x_48 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_47, x_49);
x_51 = lean_array_push(x_50, x_36);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_43, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_37, 0, x_54);
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = l_myMacro____x40_Init_Notation___hyg_14734____closed__9;
lean_inc(x_55);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_empty___closed__1;
x_60 = lean_array_push(x_59, x_58);
x_61 = l_Array_appendCore___rarg(x_59, x_35);
lean_dec(x_35);
x_62 = l_Lean_nullKind___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_59, x_63);
x_65 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_64, x_66);
x_68 = lean_array_push(x_67, x_36);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_10);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_60, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_56);
return x_72;
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFun), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_expandFun___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_3 < x_2;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Elab_Term_Quotation_withNewLocals___rarg(x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Syntax_getId(x_20);
lean_dec(x_20);
x_22 = lean_array_push(x_4, x_21);
x_23 = 1;
x_24 = x_3 + x_23;
x_3 = x_24;
x_4 = x_22;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_3 < x_2;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__1(x_17, x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = x_3 + x_25;
x_3 = x_26;
x_4 = x_23;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
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
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_14 = l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_25 = l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_24);
return x_25;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5___rarg), 1, 0);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_precheckFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
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
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_14, x_20);
lean_dec(x_14);
x_22 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_42 = lean_st_ref_get(x_8, x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_7, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 5);
lean_inc(x_47);
lean_inc(x_45);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_48, 0, x_45);
lean_inc(x_46);
x_49 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_49, 0, x_46);
lean_inc(x_45);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_50, 0, x_45);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 6, 3);
lean_closure_set(x_51, 0, x_45);
lean_closure_set(x_51, 1, x_46);
lean_closure_set(x_51, 2, x_47);
lean_inc(x_45);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_52, 0, x_45);
lean_closure_set(x_52, 1, x_46);
lean_closure_set(x_52, 2, x_47);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
x_54 = x_53;
x_55 = lean_ctor_get(x_7, 3);
lean_inc(x_55);
x_56 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_44);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_7, 2);
lean_inc(x_60);
x_61 = lean_st_ref_get(x_8, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_environment_main_module(x_45);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_57);
lean_ctor_set(x_66, 3, x_59);
lean_ctor_set(x_66, 4, x_60);
lean_ctor_set(x_66, 5, x_55);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Elab_Term_expandFunBinders(x_22, x_21, x_66, x_68);
lean_dec(x_22);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_st_ref_take(x_8, x_63);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_74, 1);
lean_dec(x_77);
lean_ctor_set(x_74, 1, x_72);
x_78 = lean_st_ref_set(x_8, x_74, x_75);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_dec(x_71);
x_81 = l_List_reverse___rarg(x_80);
x_82 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__5(x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_23 = x_70;
x_24 = x_83;
goto block_41;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_74, 0);
x_85 = lean_ctor_get(x_74, 2);
x_86 = lean_ctor_get(x_74, 3);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_74);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_72);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set(x_87, 3, x_86);
x_88 = lean_st_ref_set(x_8, x_87, x_75);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_dec(x_71);
x_91 = l_List_reverse___rarg(x_90);
x_92 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__5(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_23 = x_70;
x_24 = x_93;
goto block_41;
}
block_41:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_get_size(x_26);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__2(x_26, x_29, x_30, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_35, 0, x_27);
x_36 = l_Lean_Elab_Term_Quotation_withNewLocals___rarg(x_33, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__2(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_precheckFun), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_24 = l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabFun___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_3, x_12, x_12, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_Meta_mkLambdaFVars(x_2, x_14, x_16, x_12, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
x_18 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
lean_inc(x_1);
x_19 = l_Lean_Syntax_isOfKind(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l_myMacro____x40_Init_Notation___hyg_14734____closed__12;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_22, x_26);
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_22, x_28);
lean_dec(x_22);
x_30 = l_Lean_Syntax_getArgs(x_27);
lean_dec(x_27);
x_31 = lean_st_ref_get(x_8, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_7, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 5);
lean_inc(x_36);
lean_inc(x_34);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_37, 0, x_34);
lean_inc(x_35);
x_38 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_38, 0, x_35);
lean_inc(x_34);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_39, 0, x_34);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 6, 3);
lean_closure_set(x_40, 0, x_34);
lean_closure_set(x_40, 1, x_35);
lean_closure_set(x_40, 2, x_36);
lean_inc(x_34);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_41, 0, x_34);
lean_closure_set(x_41, 1, x_35);
lean_closure_set(x_41, 2, x_36);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_41);
x_43 = x_42;
x_44 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
x_45 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_33);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_7, 2);
lean_inc(x_49);
x_50 = lean_st_ref_get(x_8, x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_environment_main_module(x_34);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_48);
lean_ctor_set(x_55, 4, x_49);
lean_ctor_set(x_55, 5, x_44);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Term_expandFunBinders(x_30, x_29, x_55, x_57);
lean_dec(x_30);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_st_ref_take(x_8, x_52);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_63, 1);
lean_dec(x_66);
lean_ctor_set(x_63, 1, x_61);
x_67 = lean_st_ref_set(x_8, x_63, x_64);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_dec(x_60);
x_70 = l_List_reverse___rarg(x_69);
x_71 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_10 = x_59;
x_11 = x_72;
goto block_17;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_63, 0);
x_74 = lean_ctor_get(x_63, 2);
x_75 = lean_ctor_get(x_63, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_63);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_61);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_75);
x_77 = lean_st_ref_set(x_8, x_76, x_64);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_dec(x_60);
x_80 = l_List_reverse___rarg(x_79);
x_81 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_10 = x_59;
x_11 = x_82;
goto block_17;
}
}
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun___lambda__1), 10, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_elabFunBinders___rarg(x_13, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_13);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_myMacro____x40_Init_Notation___hyg_14734____closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_elabLetDeclAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg), 11, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to infer 'let' declaration type");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_elabType(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3;
x_16 = l_Lean_Elab_Term_registerCustomErrorIfMVar(x_13, x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_19 = lean_box(0);
x_20 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Elab_Term_elabTermEnsuringType(x_3, x_18, x_20, x_20, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
lean_inc(x_7);
lean_inc(x_4);
x_25 = l_Lean_Meta_mkForallFVars(x_4, x_13, x_24, x_20, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_4);
x_28 = l_Lean_Meta_mkLambdaFVars(x_4, x_22, x_24, x_24, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_array_get_size(x_4);
lean_dec(x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_array_get_size(x_4);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_26);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
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
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
return x_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_dec(x_16);
x_53 = 0;
x_54 = 1;
lean_inc(x_7);
lean_inc(x_4);
x_55 = l_Lean_Meta_mkForallFVars(x_4, x_13, x_53, x_54, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = 0;
x_60 = lean_box(0);
x_61 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_58, x_59, x_60, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_array_get_size(x_4);
lean_dec(x_4);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_array_get_size(x_4);
lean_dec(x_4);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_55);
if (x_73 == 0)
{
return x_55;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_55, 0);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_55);
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
uint8_t x_77; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_12);
if (x_77 == 0)
{
return x_12;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_12);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected error when elaborating 'let'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_box(0);
x_14 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_12, x_14, x_14, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
lean_inc(x_7);
x_19 = l_Lean_Meta_mkLambdaFVars(x_3, x_16, x_18, x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_isExprDefEq(x_2, x_20, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__2;
x_27 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
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
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
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
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_1 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__2), 11, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_4);
x_17 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_5, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_6);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_3, x_15, x_15, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
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
x_19 = l_Lean_Meta_instantiateMVars(x_17, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkOptionalNode___closed__2;
x_23 = lean_array_push(x_22, x_4);
x_24 = 0;
x_25 = l_Lean_Meta_mkLambdaFVars(x_23, x_20, x_24, x_24, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1258____closed__1;
x_2 = l_myMacro____x40_Init_Notation___hyg_16821____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___closed__1;
x_2 = l_Lean_Elab_Term_elabLetDeclAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(x_8);
lean_inc(x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed), 11, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Elab_Term_elabBinders___rarg(x_2, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_49; lean_object* x_50; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_68 = lean_st_ref_get(x_14, x_21);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = 0;
x_49 = x_73;
x_50 = x_72;
goto block_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_76 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_75, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_49 = x_79;
x_50 = x_78;
goto block_67;
}
block_48:
{
if (x_7 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = l_Lean_Syntax_getId(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__4), 11, 3);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_5);
lean_closure_set(x_27, 2, x_6);
x_28 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_29 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_26, x_28, x_22, x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_23);
x_32 = l_Lean_mkApp(x_30, x_23);
x_33 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3(x_8, x_24, x_4, x_23, x_22, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
x_38 = l_Lean_Syntax_getId(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__4), 11, 3);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_5);
lean_closure_set(x_39, 2, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_23);
lean_inc(x_22);
x_40 = l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_38, x_22, x_23, x_39, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3(x_8, x_24, x_4, x_23, x_22, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_42);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
}
block_67:
{
if (x_49 == 0)
{
x_25 = x_50;
goto block_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_51 = l_Lean_Syntax_getId(x_1);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_KernelException_toMessageData___closed__15;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkLeveErrorMessageCore___lambda__3___closed__5;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_22);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_22);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_23);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_23);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
x_64 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_65 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_64, x_63, x_9, x_10, x_11, x_12, x_13, x_14, x_50);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_25 = x_66;
goto block_48;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_18);
if (x_80 == 0)
{
return x_18;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_18, 0);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_18);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_elabLetDeclAux___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Elab_Term_expandOptType(x_1, x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkLetIdDeclView(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = 0;
x_7 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_5, x_6, x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_termIfLet___x3a_x3d__Then__Else_____closed__7;
x_17 = l_Lean_mkAtomFrom(x_1, x_16);
x_18 = l_Lean_Elab_Term_mkExplicitBinder___closed__1;
x_19 = lean_array_push(x_18, x_11);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_17);
x_23 = lean_array_push(x_22, x_9);
x_24 = l_myMacro____x40_Init_Notation___hyg_16821____closed__6;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
x_34 = l_termIfLet___x3a_x3d__Then__Else_____closed__7;
x_35 = l_Lean_mkAtomFrom(x_1, x_34);
x_36 = l_Lean_Elab_Term_mkExplicitBinder___closed__1;
x_37 = lean_array_push(x_36, x_29);
x_38 = lean_array_push(x_37, x_31);
x_39 = lean_array_push(x_38, x_33);
x_40 = lean_array_push(x_39, x_35);
x_41 = lean_array_push(x_40, x_26);
x_42 = l_myMacro____x40_Init_Notation___hyg_16821____closed__6;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
}
}
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandLetEqnsDecl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclCore_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_6, x_9);
return x_10;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_3, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.elabLetDeclCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__1;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__1;
x_3 = lean_unsigned_to_nat(623u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_13, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_inc(x_23);
x_26 = l_Lean_Syntax_getKind(x_23);
x_27 = l_myMacro____x40_Init_Notation___hyg_16821____closed__6;
x_28 = lean_name_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Parser_Term_letPatDecl___closed__2;
x_30 = lean_name_eq(x_26, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
x_31 = l_Lean_Parser_Term_letEqnsDecl___closed__2;
x_32 = lean_name_eq(x_26, x_31);
lean_dec(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_34 = lean_st_ref_get(x_10, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_9, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 5);
lean_inc(x_39);
lean_inc(x_37);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_40, 0, x_37);
lean_inc(x_38);
x_41 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_41, 0, x_38);
lean_inc(x_37);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_42, 0, x_37);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 6, 3);
lean_closure_set(x_43, 0, x_37);
lean_closure_set(x_43, 1, x_38);
lean_closure_set(x_43, 2, x_39);
lean_inc(x_37);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_44, 0, x_37);
lean_closure_set(x_44, 1, x_38);
lean_closure_set(x_44, 2, x_39);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_44);
x_46 = x_45;
x_47 = lean_ctor_get(x_9, 3);
lean_inc(x_47);
x_48 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_36);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_9, 2);
lean_inc(x_52);
x_53 = lean_st_ref_get(x_10, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_environment_main_module(x_37);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_49);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_52);
lean_ctor_set(x_58, 5, x_47);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Term_expandLetEqnsDecl(x_23, x_58, x_60);
lean_dec(x_23);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_st_ref_take(x_10, x_55);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_66, 1);
lean_dec(x_69);
lean_ctor_set(x_66, 1, x_64);
x_70 = lean_st_ref_set(x_10, x_66, x_67);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_dec(x_63);
x_73 = l_List_reverse___rarg(x_72);
x_74 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_14 = x_62;
x_15 = x_75;
goto block_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_66, 0);
x_77 = lean_ctor_get(x_66, 2);
x_78 = lean_ctor_get(x_66, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_66);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_64);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_st_ref_set(x_10, x_79, x_67);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_63, 1);
lean_inc(x_82);
lean_dec(x_63);
x_83 = l_List_reverse___rarg(x_82);
x_84 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_83, x_5, x_6, x_7, x_8, x_9, x_10, x_81);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_14 = x_62;
x_15 = x_85;
goto block_21;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_26);
lean_dec(x_13);
x_86 = l_Lean_Syntax_getArg(x_23, x_22);
x_87 = lean_unsigned_to_nat(2u);
x_88 = l_Lean_Syntax_getArg(x_23, x_87);
x_89 = l_Lean_Elab_Term_expandOptType(x_1, x_88);
lean_dec(x_88);
x_90 = lean_unsigned_to_nat(4u);
x_91 = l_Lean_Syntax_getArg(x_23, x_90);
lean_dec(x_23);
x_92 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_11);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_myMacro____x40_Init_Notation___hyg_16821____closed__1;
lean_inc(x_93);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Array_empty___closed__1;
x_104 = lean_array_push(x_103, x_102);
x_105 = l_Lean_Meta_mkArrow___closed__2;
x_106 = l_Lean_addMacroScope(x_99, x_105, x_96);
x_107 = lean_box(0);
x_108 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_93);
x_109 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_inc(x_109);
x_110 = lean_array_push(x_103, x_109);
x_111 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_112 = lean_array_push(x_110, x_111);
x_113 = l_myMacro____x40_Init_Notation___hyg_16268____closed__9;
lean_inc(x_93);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_93);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_push(x_103, x_114);
x_116 = lean_array_push(x_115, x_89);
x_117 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_103, x_118);
x_120 = l_Lean_nullKind___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_112, x_121);
x_123 = l_myMacro____x40_Init_Notation___hyg_16821____closed__11;
lean_inc(x_93);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_93);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_122, x_124);
x_126 = lean_array_push(x_125, x_91);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_27);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_array_push(x_103, x_127);
x_129 = l_myMacro____x40_Init_Notation___hyg_16821____closed__4;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_104, x_130);
x_132 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
lean_inc(x_93);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_93);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_push(x_103, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_120);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_131, x_135);
x_137 = l_myMacro____x40_Init_Notation___hyg_15342____closed__1;
lean_inc(x_93);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_93);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_push(x_103, x_138);
x_140 = lean_array_push(x_139, x_111);
x_141 = l_myMacro____x40_Init_Notation___hyg_15342____closed__5;
x_142 = lean_array_push(x_141, x_109);
x_143 = l_myMacro____x40_Init_Notation___hyg_15342____closed__4;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_array_push(x_103, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_120);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_array_push(x_140, x_146);
x_148 = lean_array_push(x_147, x_111);
x_149 = l_myMacro____x40_Init_Notation___hyg_15342____closed__6;
lean_inc(x_93);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_93);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_array_push(x_148, x_150);
x_152 = l_myMacro____x40_Init_Notation___hyg_15342____closed__11;
lean_inc(x_93);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_93);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_push(x_103, x_153);
x_155 = lean_array_push(x_103, x_86);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_120);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_array_push(x_154, x_156);
x_158 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_93);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_array_push(x_157, x_159);
x_161 = lean_array_push(x_160, x_25);
x_162 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_array_push(x_103, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_120);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_array_push(x_103, x_165);
x_167 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_array_push(x_151, x_168);
x_170 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_array_push(x_136, x_171);
x_173 = l_myMacro____x40_Init_Notation___hyg_16821____closed__2;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
if (x_3 == 0)
{
if (x_4 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
x_176 = l_Lean_Syntax_setKind(x_174, x_175);
lean_inc(x_176);
lean_inc(x_1);
x_177 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_177, 0, x_1);
lean_closure_set(x_177, 1, x_176);
lean_closure_set(x_177, 2, x_2);
x_178 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_176, x_177, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_174);
x_179 = l_Lean_instInhabitedSyntax;
x_180 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_181 = lean_panic_fn(x_179, x_180);
lean_inc(x_181);
lean_inc(x_1);
x_182 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_182, 0, x_1);
lean_closure_set(x_182, 1, x_181);
lean_closure_set(x_182, 2, x_2);
x_183 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_181, x_182, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
return x_183;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_inc(x_174);
lean_inc(x_1);
x_184 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_184, 0, x_1);
lean_closure_set(x_184, 1, x_174);
lean_closure_set(x_184, 2, x_2);
x_185 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_174, x_184, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = l_Lean_Parser_Term_let__delayed___elambda__1___closed__2;
x_187 = l_Lean_Syntax_setKind(x_174, x_186);
lean_inc(x_187);
lean_inc(x_1);
x_188 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_188, 0, x_1);
lean_closure_set(x_188, 1, x_187);
lean_closure_set(x_188, 2, x_2);
x_189 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_187, x_188, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
return x_189;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_1);
x_190 = l_Lean_Elab_Term_mkLetIdDeclView(x_23);
lean_dec(x_23);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 3);
lean_inc(x_194);
lean_dec(x_190);
x_195 = l_Lean_Elab_Term_elabLetDeclAux(x_191, x_192, x_193, x_194, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_195;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_setArg(x_13, x_16, x_14);
lean_inc(x_1);
x_18 = l_Lean_Syntax_setArg(x_1, x_12, x_17);
lean_inc(x_18);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_2);
x_20 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDecl), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_myMacro____x40_Init_Notation___hyg_16821____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetFunDecl), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDelayedDecl), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_let__delayed___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_6082_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabLetDeclAux___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Quotation_Precheck(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Binders(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation_Precheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__2___lambda__1___closed__6);
l_Lean_Elab_Term_quoteAutoTactic___closed__1 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__1);
l_Lean_Elab_Term_quoteAutoTactic___closed__2 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__2);
l_Lean_Elab_Term_quoteAutoTactic___closed__3 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__3);
l_Lean_Elab_Term_quoteAutoTactic___closed__4 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__4);
l_Lean_Elab_Term_quoteAutoTactic___closed__5 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__5);
l_Lean_Elab_Term_quoteAutoTactic___closed__6 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__6);
l_Lean_Elab_Term_quoteAutoTactic___closed__7 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__7);
l_Lean_Elab_Term_quoteAutoTactic___closed__8 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__8);
l_Lean_Elab_Term_quoteAutoTactic___closed__9 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__9);
l_Lean_Elab_Term_quoteAutoTactic___closed__10 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__10);
l_Lean_Elab_Term_quoteAutoTactic___closed__11 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__11);
l_Lean_Elab_Term_quoteAutoTactic___closed__12 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__12);
l_Lean_Elab_Term_quoteAutoTactic___closed__13 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__13);
l_Lean_Elab_Term_quoteAutoTactic___closed__14 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__14);
l_Lean_Elab_Term_quoteAutoTactic___closed__15 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__15);
l_Lean_Elab_Term_quoteAutoTactic___closed__16 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__16);
l_Lean_Elab_Term_quoteAutoTactic___closed__17 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__17);
l_Lean_Elab_Term_quoteAutoTactic___closed__18 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__18);
l_Lean_Elab_Term_quoteAutoTactic___closed__19 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__19);
l_Lean_Elab_Term_quoteAutoTactic___closed__20 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__20);
l_Lean_Elab_Term_quoteAutoTactic___closed__21 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__21();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__21);
l_Lean_Elab_Term_quoteAutoTactic___closed__22 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__22();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__22);
l_Lean_Elab_Term_quoteAutoTactic___closed__23 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__23();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__23);
l_Lean_Elab_Term_quoteAutoTactic___closed__24 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__24();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__24);
l_Lean_Elab_Term_quoteAutoTactic___closed__25 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__25();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__25);
l_Lean_Elab_Term_quoteAutoTactic___closed__26 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__26();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__26);
l_Lean_Elab_Term_quoteAutoTactic___closed__27 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__27();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__27);
l_Lean_Elab_Term_quoteAutoTactic___closed__28 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__28();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__28);
l_Lean_Elab_Term_quoteAutoTactic___closed__29 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__29();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__29);
l_Lean_Elab_Term_declareTacticSyntax___closed__1 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__1);
l_Lean_Elab_Term_declareTacticSyntax___closed__2 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__2);
l_Lean_Elab_Term_declareTacticSyntax___closed__3 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__3);
l_Lean_Elab_Term_declareTacticSyntax___closed__4 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__4);
l_Lean_Elab_Term_declareTacticSyntax___closed__5 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__3);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__4 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189____closed__4);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_checkBinderAnnotations = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_checkBinderAnnotations);
lean_dec_ref(res);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabArrow___closed__1 = _init_l_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__1);
l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_FunBinders_State_fvars___default = _init_l_Lean_Elab_Term_FunBinders_State_fvars___default();
lean_mark_persistent(l_Lean_Elab_Term_FunBinders_State_fvars___default);
l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default = _init_l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default();
lean_mark_persistent(l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default);
l_Lean_Elab_Term_expandWhereDecls___closed__1 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2);
l___regBuiltin_Lean_Elab_Term_expandFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandFun___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1);
res = l___regBuiltin_Lean_Elab_Term_precheckFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabFun___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3);
l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__3);
l_Lean_Elab_Term_elabLetDeclCore___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__1);
l_Lean_Elab_Term_elabLetDeclCore___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_6082_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
