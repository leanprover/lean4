// Lean compiler output
// Module: Lean.Elab.Binders
// Imports: Init Lean.Elab.Term Lean.Parser.Term
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__6;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__4;
lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_term_____x5b___x3a___x5d___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__3;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__3;
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__2(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__25;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letEqnsDecl___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__5;
lean_object* l_Lean_Elab_Term_elabLetDeclAux_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__1;
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1090____closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__4;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___boxed(lean_object**);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__4;
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letPatDecl___closed__2;
lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__8;
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2;
lean_object* l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_5198____spec__1(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3;
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__22;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__18;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__15;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeWithAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_whereDecls_formatter___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_binderTactic___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2;
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__3;
extern lean_object* l_Array_forInUnsafe_loop___at___private_Init_NotationExtra_0__Lean_mkHintBody___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__14;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__28;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___closed__2;
lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__5;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_5431_(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__20;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfoCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4;
lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__10;
lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__24;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__7;
extern lean_object* l_termIfLet___x3a_x3d__Then__Else_____closed__7;
lean_object* l___private_Init_Meta_0__Lean_quoteName(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabForall(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let__delayed___elambda__1___closed__2;
extern lean_object* l_instMonadEST___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__19;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15440____closed__8;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__2(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5;
lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__3(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
extern lean_object* l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__26;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__5;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__1;
lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default;
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__16;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__3;
extern lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17279____closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1;
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__2___boxed(lean_object**);
extern lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabLetDeclCore_match__2(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1;
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addTermInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2;
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__23;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__1;
extern lean_object* l_Lean_Parser_Term_binderDefault___elambda__1___closed__2;
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFun_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1272____closed__7;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__2;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__17;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__2;
extern lean_object* l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__4;
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__4;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
extern lean_object* l_Lean_Parser_Tactic_intro___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__2;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__21;
lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_FunBinders_State_fvars___default;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__13;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__27;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
extern lean_object* l_Lean_Parser_Term_letRecDecl___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__9;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLetDeclAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
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
x_12 = l_Lean_Elab_Term_mkFreshIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_12;
}
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_24 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array.push");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("push");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, antiquotation is not allowed");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4;
x_28 = lean_name_mk_string(x_2, x_27);
lean_inc(x_28);
x_29 = l_Lean_addMacroScope(x_26, x_28, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3;
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
x_41 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
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
x_46 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4;
x_47 = lean_name_mk_string(x_2, x_46);
lean_inc(x_47);
x_48 = l_Lean_addMacroScope(x_44, x_47, x_22);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_3);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3;
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
x_60 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
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
x_70 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6;
x_71 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_1, x_70, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_24, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_25;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_24 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___boxed), 13, 6);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_5);
lean_closure_set(x_24, 3, x_6);
lean_closure_set(x_24, 4, x_10);
lean_closure_set(x_24, 5, x_1);
x_25 = lean_box_usize(x_9);
x_26 = lean_box_usize(x_8);
x_27 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__2___boxed), 17, 9);
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
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_24 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
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
x_3 = lean_unsigned_to_nat(58u);
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
x_1 = l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array.empty");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("empty");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_term_____x5b___x3a___x5d___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax.node");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__12;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__13;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Syntax_addPrec___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_2 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
x_2 = l_Lean_Meta_DiscrTree_Trie_format___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAtom");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__24;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, identifier is not allowed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__27;
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
x_30 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_31 = l_Lean_addMacroScope(x_28, x_30, x_25);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
x_34 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_array_get_size(x_14);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = 0;
x_39 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
x_40 = l_Array_term_____x5b___x3a___x5d___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_13, x_39, x_20, x_40, x_32, x_32, x_14, x_37, x_38, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_43);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_Elab_Term_quoteAutoTactic___closed__16;
x_54 = l_Lean_addMacroScope(x_52, x_53, x_48);
x_55 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_56 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_56);
x_58 = l_Array_empty___closed__1;
x_59 = lean_array_push(x_58, x_57);
x_60 = l___private_Init_Meta_0__Lean_quoteName(x_13);
x_61 = lean_array_push(x_58, x_60);
x_62 = lean_array_push(x_61, x_42);
x_63 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_63);
x_64 = lean_array_push(x_59, x_1);
x_65 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_50, 0, x_66);
return x_50;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_50, 0);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_50);
x_69 = l_Lean_Elab_Term_quoteAutoTactic___closed__16;
x_70 = l_Lean_addMacroScope(x_67, x_69, x_48);
x_71 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_72 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_45);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
x_74 = l_Array_empty___closed__1;
x_75 = lean_array_push(x_74, x_73);
x_76 = l___private_Init_Meta_0__Lean_quoteName(x_13);
x_77 = lean_array_push(x_74, x_76);
x_78 = lean_array_push(x_77, x_42);
x_79 = l_Lean_nullKind___closed__2;
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_79);
x_80 = lean_array_push(x_75, x_1);
x_81 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_68);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_41);
if (x_84 == 0)
{
return x_41;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_41, 0);
x_86 = lean_ctor_get(x_41, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_41);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_88 = l_Lean_Elab_Term_instMonadQuotationTermElabM;
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_8);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_100 = l_Lean_addMacroScope(x_97, x_99, x_94);
x_101 = lean_box(0);
x_102 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
x_103 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_100);
lean_ctor_set(x_104, 3, x_103);
x_105 = lean_array_get_size(x_14);
x_106 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_107 = 0;
x_108 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
x_109 = l_Array_term_____x5b___x3a___x5d___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_110 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_13, x_108, x_89, x_109, x_101, x_101, x_14, x_106, x_107, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_115);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_118);
lean_dec(x_7);
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
x_123 = l_Lean_Elab_Term_quoteAutoTactic___closed__16;
x_124 = l_Lean_addMacroScope(x_120, x_123, x_117);
x_125 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_126 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_127 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_127, 0, x_114);
lean_ctor_set(x_127, 1, x_125);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_126);
x_128 = l_Array_empty___closed__1;
x_129 = lean_array_push(x_128, x_127);
x_130 = l___private_Init_Meta_0__Lean_quoteName(x_13);
x_131 = lean_array_push(x_128, x_130);
x_132 = lean_array_push(x_131, x_111);
x_133 = l_Lean_nullKind___closed__2;
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_array_push(x_129, x_134);
x_136 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
if (lean_is_scalar(x_122)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_122;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_121);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_143; lean_object* x_144; 
lean_dec(x_14);
lean_dec(x_13);
x_143 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6;
x_144 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5(x_1, x_143, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_144;
}
}
case 2:
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_1);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_146 = lean_ctor_get(x_1, 1);
x_147 = lean_ctor_get(x_1, 0);
lean_dec(x_147);
x_148 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_8);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_153);
lean_dec(x_7);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_158 = l_Lean_addMacroScope(x_156, x_157, x_152);
x_159 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
x_160 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_161 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_161, 0, x_149);
lean_ctor_set(x_161, 1, x_159);
lean_ctor_set(x_161, 2, x_158);
lean_ctor_set(x_161, 3, x_160);
x_162 = l_Array_empty___closed__1;
x_163 = lean_array_push(x_162, x_161);
x_164 = lean_box(2);
x_165 = l_Lean_Syntax_mkStrLit(x_146, x_164);
lean_dec(x_146);
x_166 = lean_array_push(x_162, x_165);
x_167 = l_Lean_nullKind___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_166);
lean_ctor_set(x_1, 0, x_167);
x_168 = lean_array_push(x_163, x_1);
x_169 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_154, 0, x_170);
return x_154;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_171 = lean_ctor_get(x_154, 0);
x_172 = lean_ctor_get(x_154, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_154);
x_173 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_174 = l_Lean_addMacroScope(x_171, x_173, x_152);
x_175 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
x_176 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_177 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_177, 0, x_149);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_174);
lean_ctor_set(x_177, 3, x_176);
x_178 = l_Array_empty___closed__1;
x_179 = lean_array_push(x_178, x_177);
x_180 = lean_box(2);
x_181 = l_Lean_Syntax_mkStrLit(x_146, x_180);
lean_dec(x_146);
x_182 = lean_array_push(x_178, x_181);
x_183 = l_Lean_nullKind___closed__2;
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_182);
lean_ctor_set(x_1, 0, x_183);
x_184 = lean_array_push(x_179, x_1);
x_185 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_172);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
lean_dec(x_1);
x_189 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_8);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_191);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_194);
lean_dec(x_7);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_200 = l_Lean_addMacroScope(x_196, x_199, x_193);
x_201 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
x_202 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_203 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_203, 0, x_190);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_200);
lean_ctor_set(x_203, 3, x_202);
x_204 = l_Array_empty___closed__1;
x_205 = lean_array_push(x_204, x_203);
x_206 = lean_box(2);
x_207 = l_Lean_Syntax_mkStrLit(x_188, x_206);
lean_dec(x_188);
x_208 = lean_array_push(x_204, x_207);
x_209 = l_Lean_nullKind___closed__2;
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_array_push(x_205, x_210);
x_212 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
if (lean_is_scalar(x_198)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_198;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_197);
return x_214;
}
}
default: 
{
lean_object* x_215; lean_object* x_216; 
x_215 = l_Lean_Elab_Term_quoteAutoTactic___closed__28;
x_216 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5(x_1, x_215, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_216;
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__2___boxed(lean_object** _args) {
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
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__2(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___boxed(lean_object** _args) {
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
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
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
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1090____closed__1;
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
x_49 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__7(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
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
x_131 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__7(x_128, x_101, x_3, x_4, x_5, x_6, x_7, x_130);
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
x_222 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__7(x_219, x_192, x_3, x_4, x_5, x_6, x_7, x_221);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg), 1, 0);
return x_7;
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
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_9);
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
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_7, x_8, x_23);
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
x_46 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
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
x_63 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
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
x_72 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_7, x_8, x_9);
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
x_93 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
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
x_109 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
x_21 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
x_22 = lean_name_eq(x_18, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2;
x_24 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__5(x_17, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder_match__1___rarg), 3, 0);
return x_2;
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
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_expandExplicitBindersAux_loop___closed__2;
x_12 = lean_name_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_14 = lean_name_eq(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_16 = lean_name_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
x_18 = lean_name_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = l_Lean_instInhabitedSyntax;
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_array_get(x_20, x_10, x_21);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_array_get(x_20, x_10, x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
x_30 = l_Lean_mkOptionalNode___closed__2;
x_31 = lean_array_push(x_30, x_29);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_array_get(x_20, x_10, x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_36);
x_38 = l_Lean_mkOptionalNode___closed__2;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lean_instInhabitedSyntax;
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_array_get(x_41, x_10, x_42);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_44 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_array_get(x_41, x_10, x_47);
x_49 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_48);
lean_dec(x_48);
x_50 = lean_array_get_size(x_45);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = x_45;
x_53 = lean_box_usize(x_51);
x_54 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_55 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed), 11, 4);
lean_closure_set(x_55, 0, x_49);
lean_closure_set(x_55, 1, x_53);
lean_closure_set(x_55, 2, x_54);
lean_closure_set(x_55, 3, x_52);
x_56 = x_55;
x_57 = lean_apply_7(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
return x_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_44, 0);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_44);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_Lean_instInhabitedSyntax;
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_array_get(x_62, x_10, x_63);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_65 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_array_get(x_62, x_10, x_68);
x_70 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_69);
lean_dec(x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_array_get(x_62, x_10, x_71);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(x_70, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_array_get_size(x_66);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = x_66;
x_79 = lean_box_usize(x_77);
x_80 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_81 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed), 11, 4);
lean_closure_set(x_81, 0, x_74);
lean_closure_set(x_81, 1, x_79);
lean_closure_set(x_81, 2, x_80);
lean_closure_set(x_81, 3, x_78);
x_82 = x_81;
x_83 = lean_apply_7(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_73);
if (x_84 == 0)
{
return x_73;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_73, 0);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_73);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_65);
if (x_88 == 0)
{
return x_65;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_65, 0);
x_90 = lean_ctor_get(x_65, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_65);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = l_Lean_instInhabitedSyntax;
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_array_get(x_92, x_10, x_93);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_95 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_array_get(x_92, x_10, x_98);
x_100 = l_Lean_Elab_Term_expandOptType(x_1, x_99);
lean_dec(x_99);
x_101 = lean_array_get_size(x_96);
x_102 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_103 = x_96;
x_104 = lean_box_usize(x_102);
x_105 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_106 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed), 11, 4);
lean_closure_set(x_106, 0, x_100);
lean_closure_set(x_106, 1, x_104);
lean_closure_set(x_106, 2, x_105);
lean_closure_set(x_106, 3, x_103);
x_107 = x_106;
x_108 = lean_apply_7(x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_97);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
return x_95;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_95, 0);
x_111 = lean_ctor_get(x_95, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_95);
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
lean_object* x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(x_8);
return x_113;
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
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
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_10);
lean_inc(x_7);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_array_push(x_3, x_7);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_4, x_5, x_6, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_20;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_8, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = l_Lean_Syntax_getId(x_18);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_21 = lean_box(x_6);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed), 14, 6);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_21);
lean_closure_set(x_22, 5, x_7);
x_23 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_19, x_20, x_8, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
return x_23;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_apply_8(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_1, x_4);
lean_inc(x_10);
lean_inc(x_6);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
if (x_2 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_20 = l_Lean_Elab_Term_elabType(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
x_26 = l_Lean_Syntax_getId(x_25);
x_27 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_dec(x_16);
x_28 = lean_box(x_2);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed), 14, 6);
lean_closure_set(x_29, 0, x_25);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_5);
lean_closure_set(x_29, 3, x_1);
lean_closure_set(x_29, 4, x_28);
lean_closure_set(x_29, 5, x_3);
x_30 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_26, x_27, x_21, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_19);
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
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
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
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
x_37 = lean_box(x_2);
lean_inc(x_36);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed), 15, 7);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_16);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_5);
lean_closure_set(x_38, 4, x_1);
lean_closure_set(x_38, 5, x_37);
lean_closure_set(x_38, 6, x_3);
x_39 = l_Lean_Elab_Term_elabTypeWithAutoBoundImplicit___rarg(x_36, x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
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
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_1, x_2, x_4, x_12, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_apply_8(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
x_22 = lean_box(x_2);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed), 12, 4);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_18, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(x_1, x_2, x_3, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Meta_getResetPostponed(x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_processPostponed(x_22, x_6, x_7, x_8, x_9, x_21);
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
lean_dec(x_20);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_setPostponed(x_17, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_37 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(x_17, x_20, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_11 = x_38;
x_12 = x_39;
goto block_15;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
x_40 = lean_ctor_get(x_23, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = l_Lean_Meta_setPostponed(x_17, x_6, x_7, x_8, x_9, x_41);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
x_47 = lean_ctor_get(x_19, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_dec(x_19);
x_49 = l_Lean_Meta_setPostponed(x_17, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = l_Array_empty___closed__1;
x_14 = lean_apply_1(x_2, x_13);
x_15 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabBinders___spec__1___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_mkOptionalNode___closed__2;
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = l_Lean_Elab_Term_elabBinders___rarg(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg___boxed), 10, 0);
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
lean_object* l_Lean_Elab_Term_elabBinder___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Term_elabBinder___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 9, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = 0;
x_20 = l_Lean_Elab_Term_elabBinders___rarg(x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
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
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
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
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_8);
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
x_32 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_33 = l_Lean_addMacroScope(x_24, x_32, x_20);
x_34 = lean_box(0);
x_35 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
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
x_41 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
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
x_47 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
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
x_57 = l_myMacro____x40_Init_Notation___hyg_1272____closed__7;
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
x_72 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_73 = l_Lean_addMacroScope(x_63, x_72, x_20);
x_74 = lean_box(0);
x_75 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
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
x_81 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
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
x_87 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
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
x_97 = l_myMacro____x40_Init_Notation___hyg_1272____closed__7;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_mkOptionalNode___closed__2;
x_15 = lean_array_push(x_14, x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 9, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = 0;
x_18 = l_Lean_Elab_Term_elabBinders___rarg(x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_23; 
x_23 = x_4 < x_3;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_array_uget(x_2, x_4);
x_27 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
lean_inc(x_1);
x_28 = lean_name_mk_string(x_1, x_27);
lean_inc(x_26);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_identKind___closed__2;
lean_inc(x_26);
x_31 = l_Lean_Syntax_isOfKind(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_box(0);
x_13 = x_32;
x_14 = x_12;
goto block_22;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_26);
x_13 = x_33;
x_14 = x_12;
goto block_22;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_6);
x_34 = l_Lean_Elab_Term_mkFreshIdent(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_13 = x_37;
x_14 = x_36;
goto block_22;
}
}
block_22:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_push(x_5, x_17);
x_19 = 1;
x_20 = x_4 + x_19;
x_4 = x_20;
x_5 = x_18;
x_12 = x_14;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_24; uint8_t x_25; 
x_24 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
lean_inc(x_1);
x_25 = l_Lean_Syntax_isOfKind(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
lean_inc(x_1);
x_27 = l_Lean_Syntax_isOfKind(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_2);
x_28 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_29 = l_Lean_Syntax_isOfKind(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_box(0);
x_9 = x_30;
x_10 = x_8;
goto block_23;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_9 = x_31;
x_10 = x_8;
goto block_23;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Elab_Term_mkFreshIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_9 = x_35;
x_10 = x_34;
goto block_23;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_71; uint8_t x_72; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Syntax_getArg(x_1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
lean_dec(x_1);
x_40 = l_Lean_Syntax_getArgs(x_39);
lean_dec(x_39);
x_71 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
lean_inc(x_37);
x_72 = l_Lean_Syntax_isOfKind(x_37, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_identKind___closed__2;
lean_inc(x_37);
x_74 = l_Lean_Syntax_isOfKind(x_37, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_37);
x_75 = lean_box(0);
x_41 = x_75;
x_42 = x_8;
goto block_70;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_37);
x_41 = x_76;
x_42 = x_8;
goto block_70;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_2);
x_77 = l_Lean_Elab_Term_mkFreshIdent(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_37);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_78);
x_41 = x_80;
x_42 = x_79;
goto block_70;
}
block_70:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_2);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Array_empty___closed__1;
x_47 = lean_array_push(x_46, x_45);
x_48 = lean_array_get_size(x_40);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = 0;
x_51 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_52 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(x_51, x_40, x_49, x_50, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
lean_dec(x_40);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_52, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_52, 0, x_64);
return x_52;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_dec(x_52);
x_66 = lean_ctor_get(x_53, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_67 = x_53;
} else {
 lean_dec_ref(x_53);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
}
}
block_23:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = l_Array_empty___closed__1;
x_16 = lean_array_push(x_15, x_14);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
x_41 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
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
x_44 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_45 = lean_string_dec_eq(x_17, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_2);
x_46 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_47 = lean_string_dec_eq(x_17, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_3);
x_48 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
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
x_52 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_53 = lean_string_dec_eq(x_17, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_6);
x_54 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
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
x_91 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
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
x_95 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_96 = lean_string_dec_eq(x_17, x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_2);
x_97 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_98 = lean_string_dec_eq(x_17, x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_3);
x_99 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
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
x_103 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_104 = lean_string_dec_eq(x_17, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_6);
x_105 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
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
x_150 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
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
x_155 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_156 = lean_string_dec_eq(x_17, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_2);
x_157 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_158 = lean_string_dec_eq(x_17, x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_3);
x_159 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
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
x_163 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_164 = lean_string_dec_eq(x_17, x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_6);
x_165 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
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
x_215 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
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
x_221 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_222 = lean_string_dec_eq(x_17, x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_2);
x_223 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_224 = lean_string_dec_eq(x_17, x_223);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; 
lean_dec(x_3);
x_225 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
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
x_229 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_230 = lean_string_dec_eq(x_17, x_229);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
lean_dec(x_6);
x_231 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
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
x_286 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
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
x_293 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_294 = lean_string_dec_eq(x_17, x_293);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
lean_dec(x_2);
x_295 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_296 = lean_string_dec_eq(x_17, x_295);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_3);
x_297 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
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
x_301 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_302 = lean_string_dec_eq(x_17, x_301);
if (x_302 == 0)
{
lean_object* x_303; uint8_t x_304; 
lean_dec(x_6);
x_303 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
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
x_363 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
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
x_371 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_372 = lean_string_dec_eq(x_340, x_371);
if (x_372 == 0)
{
lean_object* x_373; uint8_t x_374; 
lean_dec(x_2);
x_373 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_374 = lean_string_dec_eq(x_340, x_373);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
lean_dec(x_3);
x_375 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
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
x_379 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_380 = lean_string_dec_eq(x_340, x_379);
if (x_380 == 0)
{
lean_object* x_381; uint8_t x_382; 
lean_dec(x_6);
x_381 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_array_fget(x_1, x_3);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_25 = l_Lean_mkHole(x_19);
lean_inc(x_21);
x_26 = l_Lean_Elab_Term_mkExplicitBinder(x_21, x_25);
x_27 = lean_array_push(x_4, x_26);
lean_inc(x_5);
x_28 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_24, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_dec(x_36);
x_37 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_31);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_5);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_38);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_empty___closed__1;
x_48 = lean_array_push(x_47, x_46);
x_49 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_50 = lean_array_push(x_49, x_21);
x_51 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_array_push(x_47, x_52);
x_54 = l_Lean_nullKind___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_48, x_55);
x_57 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_58 = lean_array_push(x_56, x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_38);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_38);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_push(x_58, x_60);
x_62 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_38);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_38);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_47, x_63);
x_65 = lean_array_push(x_47, x_19);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_64, x_66);
x_68 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_38);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_67, x_69);
x_71 = lean_array_push(x_70, x_35);
x_72 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_47, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_54);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_47, x_75);
x_77 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_array_push(x_61, x_78);
x_80 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = 1;
x_83 = lean_box(x_82);
lean_ctor_set(x_30, 1, x_83);
lean_ctor_set(x_30, 0, x_81);
lean_ctor_set(x_42, 0, x_29);
return x_42;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
x_84 = lean_ctor_get(x_42, 1);
lean_inc(x_84);
lean_dec(x_42);
x_85 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_38);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_38);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Array_empty___closed__1;
x_88 = lean_array_push(x_87, x_86);
x_89 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_90 = lean_array_push(x_89, x_21);
x_91 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_87, x_92);
x_94 = l_Lean_nullKind___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_array_push(x_88, x_95);
x_97 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_98 = lean_array_push(x_96, x_97);
x_99 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_38);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_38);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_array_push(x_98, x_100);
x_102 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_38);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_38);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_push(x_87, x_103);
x_105 = lean_array_push(x_87, x_19);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_104, x_106);
x_108 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_38);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_push(x_107, x_109);
x_111 = lean_array_push(x_110, x_35);
x_112 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_array_push(x_87, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_94);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_87, x_115);
x_117 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_101, x_118);
x_120 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = 1;
x_123 = lean_box(x_122);
lean_ctor_set(x_30, 1, x_123);
lean_ctor_set(x_30, 0, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_29);
lean_ctor_set(x_124, 1, x_84);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_125 = lean_ctor_get(x_30, 0);
lean_inc(x_125);
lean_dec(x_30);
x_126 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_31);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_128);
lean_dec(x_5);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_130);
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
x_134 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_127);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Array_empty___closed__1;
x_137 = lean_array_push(x_136, x_135);
x_138 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_139 = lean_array_push(x_138, x_21);
x_140 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_array_push(x_136, x_141);
x_143 = l_Lean_nullKind___closed__2;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_array_push(x_137, x_144);
x_146 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_147 = lean_array_push(x_145, x_146);
x_148 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_127);
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_127);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_array_push(x_147, x_149);
x_151 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_127);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_127);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_push(x_136, x_152);
x_154 = lean_array_push(x_136, x_19);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_push(x_153, x_155);
x_157 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_127);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_array_push(x_156, x_158);
x_160 = lean_array_push(x_159, x_125);
x_161 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_array_push(x_136, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_143);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_136, x_164);
x_166 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_array_push(x_150, x_167);
x_169 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = 1;
x_172 = lean_box(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_29, 1, x_173);
if (lean_is_scalar(x_133)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_133;
}
lean_ctor_set(x_174, 0, x_29);
lean_ctor_set(x_174, 1, x_132);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_175 = lean_ctor_get(x_29, 0);
lean_inc(x_175);
lean_dec(x_29);
x_176 = lean_ctor_get(x_30, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_177 = x_30;
} else {
 lean_dec_ref(x_30);
 x_177 = lean_box(0);
}
x_178 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_31);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_180);
lean_dec(x_5);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_182);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
x_186 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_179);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_179);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Array_empty___closed__1;
x_189 = lean_array_push(x_188, x_187);
x_190 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_191 = lean_array_push(x_190, x_21);
x_192 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_array_push(x_188, x_193);
x_195 = l_Lean_nullKind___closed__2;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_array_push(x_189, x_196);
x_198 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_199 = lean_array_push(x_197, x_198);
x_200 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_179);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_179);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_array_push(x_199, x_201);
x_203 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_179);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_179);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_array_push(x_188, x_204);
x_206 = lean_array_push(x_188, x_19);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_array_push(x_205, x_207);
x_209 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_179);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_array_push(x_208, x_210);
x_212 = lean_array_push(x_211, x_176);
x_213 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_array_push(x_188, x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_195);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_array_push(x_188, x_216);
x_218 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = lean_array_push(x_202, x_219);
x_221 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
x_223 = 1;
x_224 = lean_box(x_223);
if (lean_is_scalar(x_177)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_177;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_175);
lean_ctor_set(x_226, 1, x_225);
if (lean_is_scalar(x_185)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_185;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_184);
return x_227;
}
}
case 1:
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_19, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 1)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 1)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 1)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 1)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_dec(x_230);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
lean_dec(x_231);
x_237 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_238 = lean_string_dec_eq(x_236, x_237);
lean_dec(x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_inc(x_5);
x_239 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_nat_add(x_3, x_242);
lean_dec(x_3);
x_244 = l_Lean_mkHole(x_19);
lean_inc(x_240);
x_245 = l_Lean_Elab_Term_mkExplicitBinder(x_240, x_244);
x_246 = lean_array_push(x_4, x_245);
lean_inc(x_5);
x_247 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_243, x_246, x_5, x_6, x_7, x_8, x_9, x_10, x_241);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = !lean_is_exclusive(x_248);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_248, 1);
lean_dec(x_252);
x_253 = !lean_is_exclusive(x_249);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_254 = lean_ctor_get(x_249, 0);
x_255 = lean_ctor_get(x_249, 1);
lean_dec(x_255);
x_256 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_250);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_258);
lean_dec(x_5);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_261 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_260);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_263 = lean_ctor_get(x_261, 0);
lean_dec(x_263);
x_264 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_257);
x_265 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_265, 0, x_257);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Array_empty___closed__1;
x_267 = lean_array_push(x_266, x_265);
x_268 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_269 = lean_array_push(x_268, x_240);
x_270 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_array_push(x_266, x_271);
x_273 = l_Lean_nullKind___closed__2;
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
x_275 = lean_array_push(x_267, x_274);
x_276 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_277 = lean_array_push(x_275, x_276);
x_278 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_257);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_257);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_array_push(x_277, x_279);
x_281 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_257);
x_282 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_282, 0, x_257);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_array_push(x_266, x_282);
lean_inc(x_19);
x_284 = lean_array_push(x_266, x_19);
x_285 = !lean_is_exclusive(x_19);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_286 = lean_ctor_get(x_19, 1);
lean_dec(x_286);
x_287 = lean_ctor_get(x_19, 0);
lean_dec(x_287);
lean_ctor_set(x_19, 1, x_284);
lean_ctor_set(x_19, 0, x_273);
x_288 = lean_array_push(x_283, x_19);
x_289 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_290 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_290, 0, x_257);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_array_push(x_288, x_290);
x_292 = lean_array_push(x_291, x_254);
x_293 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = lean_array_push(x_266, x_294);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_273);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_array_push(x_266, x_296);
x_298 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = lean_array_push(x_280, x_299);
x_301 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = 1;
x_304 = lean_box(x_303);
lean_ctor_set(x_249, 1, x_304);
lean_ctor_set(x_249, 0, x_302);
lean_ctor_set(x_261, 0, x_248);
return x_261;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
lean_dec(x_19);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_273);
lean_ctor_set(x_305, 1, x_284);
x_306 = lean_array_push(x_283, x_305);
x_307 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_308 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_308, 0, x_257);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_array_push(x_306, x_308);
x_310 = lean_array_push(x_309, x_254);
x_311 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
x_313 = lean_array_push(x_266, x_312);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_273);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_array_push(x_266, x_314);
x_316 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
x_318 = lean_array_push(x_280, x_317);
x_319 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = 1;
x_322 = lean_box(x_321);
lean_ctor_set(x_249, 1, x_322);
lean_ctor_set(x_249, 0, x_320);
lean_ctor_set(x_261, 0, x_248);
return x_261;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; 
x_323 = lean_ctor_get(x_261, 1);
lean_inc(x_323);
lean_dec(x_261);
x_324 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_257);
x_325 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_325, 0, x_257);
lean_ctor_set(x_325, 1, x_324);
x_326 = l_Array_empty___closed__1;
x_327 = lean_array_push(x_326, x_325);
x_328 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_329 = lean_array_push(x_328, x_240);
x_330 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
x_332 = lean_array_push(x_326, x_331);
x_333 = l_Lean_nullKind___closed__2;
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
x_335 = lean_array_push(x_327, x_334);
x_336 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_337 = lean_array_push(x_335, x_336);
x_338 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_257);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_257);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_array_push(x_337, x_339);
x_341 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_257);
x_342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_342, 0, x_257);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_array_push(x_326, x_342);
lean_inc(x_19);
x_344 = lean_array_push(x_326, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_345 = x_19;
} else {
 lean_dec_ref(x_19);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_333);
lean_ctor_set(x_346, 1, x_344);
x_347 = lean_array_push(x_343, x_346);
x_348 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_257);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_array_push(x_347, x_349);
x_351 = lean_array_push(x_350, x_254);
x_352 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_array_push(x_326, x_353);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_333);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_array_push(x_326, x_355);
x_357 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
x_359 = lean_array_push(x_340, x_358);
x_360 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
x_362 = 1;
x_363 = lean_box(x_362);
lean_ctor_set(x_249, 1, x_363);
lean_ctor_set(x_249, 0, x_361);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_248);
lean_ctor_set(x_364, 1, x_323);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_365 = lean_ctor_get(x_249, 0);
lean_inc(x_365);
lean_dec(x_249);
x_366 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_250);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_368);
lean_dec(x_5);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec(x_369);
x_371 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_370);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_373 = x_371;
} else {
 lean_dec_ref(x_371);
 x_373 = lean_box(0);
}
x_374 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_367);
x_375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_375, 0, x_367);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Array_empty___closed__1;
x_377 = lean_array_push(x_376, x_375);
x_378 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_379 = lean_array_push(x_378, x_240);
x_380 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
x_382 = lean_array_push(x_376, x_381);
x_383 = l_Lean_nullKind___closed__2;
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_array_push(x_377, x_384);
x_386 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_387 = lean_array_push(x_385, x_386);
x_388 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_367);
x_389 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_389, 0, x_367);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_array_push(x_387, x_389);
x_391 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_367);
x_392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_392, 0, x_367);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_array_push(x_376, x_392);
lean_inc(x_19);
x_394 = lean_array_push(x_376, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_395 = x_19;
} else {
 lean_dec_ref(x_19);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_383);
lean_ctor_set(x_396, 1, x_394);
x_397 = lean_array_push(x_393, x_396);
x_398 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_399 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_399, 0, x_367);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_array_push(x_397, x_399);
x_401 = lean_array_push(x_400, x_365);
x_402 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_401);
x_404 = lean_array_push(x_376, x_403);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_383);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_array_push(x_376, x_405);
x_407 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_406);
x_409 = lean_array_push(x_390, x_408);
x_410 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_409);
x_412 = 1;
x_413 = lean_box(x_412);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set(x_248, 1, x_414);
if (lean_is_scalar(x_373)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_373;
}
lean_ctor_set(x_415, 0, x_248);
lean_ctor_set(x_415, 1, x_372);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_416 = lean_ctor_get(x_248, 0);
lean_inc(x_416);
lean_dec(x_248);
x_417 = lean_ctor_get(x_249, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_418 = x_249;
} else {
 lean_dec_ref(x_249);
 x_418 = lean_box(0);
}
x_419 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_250);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_421);
lean_dec(x_5);
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
lean_dec(x_422);
x_424 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_423);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_426 = x_424;
} else {
 lean_dec_ref(x_424);
 x_426 = lean_box(0);
}
x_427 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_420);
x_428 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_428, 0, x_420);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Array_empty___closed__1;
x_430 = lean_array_push(x_429, x_428);
x_431 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_432 = lean_array_push(x_431, x_240);
x_433 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
x_435 = lean_array_push(x_429, x_434);
x_436 = l_Lean_nullKind___closed__2;
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_435);
x_438 = lean_array_push(x_430, x_437);
x_439 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_440 = lean_array_push(x_438, x_439);
x_441 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_420);
x_442 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_442, 0, x_420);
lean_ctor_set(x_442, 1, x_441);
x_443 = lean_array_push(x_440, x_442);
x_444 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_420);
x_445 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_445, 0, x_420);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_array_push(x_429, x_445);
lean_inc(x_19);
x_447 = lean_array_push(x_429, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_448 = x_19;
} else {
 lean_dec_ref(x_19);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_436);
lean_ctor_set(x_449, 1, x_447);
x_450 = lean_array_push(x_446, x_449);
x_451 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_452 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_452, 0, x_420);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_array_push(x_450, x_452);
x_454 = lean_array_push(x_453, x_417);
x_455 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
x_457 = lean_array_push(x_429, x_456);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_436);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_array_push(x_429, x_458);
x_460 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_459);
x_462 = lean_array_push(x_443, x_461);
x_463 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_462);
x_465 = 1;
x_466 = lean_box(x_465);
if (lean_is_scalar(x_418)) {
 x_467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_467 = x_418;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_416);
lean_ctor_set(x_468, 1, x_467);
if (lean_is_scalar(x_426)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_426;
}
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_425);
return x_469;
}
}
else
{
lean_object* x_470; uint8_t x_471; 
x_470 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_471 = lean_string_dec_eq(x_235, x_470);
lean_dec(x_235);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
lean_dec(x_234);
lean_dec(x_233);
lean_inc(x_5);
x_472 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_unsigned_to_nat(1u);
x_476 = lean_nat_add(x_3, x_475);
lean_dec(x_3);
x_477 = l_Lean_mkHole(x_19);
lean_inc(x_473);
x_478 = l_Lean_Elab_Term_mkExplicitBinder(x_473, x_477);
x_479 = lean_array_push(x_4, x_478);
lean_inc(x_5);
x_480 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_476, x_479, x_5, x_6, x_7, x_8, x_9, x_10, x_474);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_dec(x_480);
x_484 = !lean_is_exclusive(x_481);
if (x_484 == 0)
{
lean_object* x_485; uint8_t x_486; 
x_485 = lean_ctor_get(x_481, 1);
lean_dec(x_485);
x_486 = !lean_is_exclusive(x_482);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_487 = lean_ctor_get(x_482, 0);
x_488 = lean_ctor_get(x_482, 1);
lean_dec(x_488);
x_489 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_483);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
x_492 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_491);
lean_dec(x_5);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
x_494 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_493);
x_495 = !lean_is_exclusive(x_494);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_496 = lean_ctor_get(x_494, 0);
lean_dec(x_496);
x_497 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_490);
x_498 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_498, 0, x_490);
lean_ctor_set(x_498, 1, x_497);
x_499 = l_Array_empty___closed__1;
x_500 = lean_array_push(x_499, x_498);
x_501 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_502 = lean_array_push(x_501, x_473);
x_503 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_502);
x_505 = lean_array_push(x_499, x_504);
x_506 = l_Lean_nullKind___closed__2;
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_505);
x_508 = lean_array_push(x_500, x_507);
x_509 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_510 = lean_array_push(x_508, x_509);
x_511 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_490);
x_512 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_512, 0, x_490);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_array_push(x_510, x_512);
x_514 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_490);
x_515 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_515, 0, x_490);
lean_ctor_set(x_515, 1, x_514);
x_516 = lean_array_push(x_499, x_515);
lean_inc(x_19);
x_517 = lean_array_push(x_499, x_19);
x_518 = !lean_is_exclusive(x_19);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; 
x_519 = lean_ctor_get(x_19, 1);
lean_dec(x_519);
x_520 = lean_ctor_get(x_19, 0);
lean_dec(x_520);
lean_ctor_set(x_19, 1, x_517);
lean_ctor_set(x_19, 0, x_506);
x_521 = lean_array_push(x_516, x_19);
x_522 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_523 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_523, 0, x_490);
lean_ctor_set(x_523, 1, x_522);
x_524 = lean_array_push(x_521, x_523);
x_525 = lean_array_push(x_524, x_487);
x_526 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_525);
x_528 = lean_array_push(x_499, x_527);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_506);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_array_push(x_499, x_529);
x_531 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_530);
x_533 = lean_array_push(x_513, x_532);
x_534 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_533);
x_536 = 1;
x_537 = lean_box(x_536);
lean_ctor_set(x_482, 1, x_537);
lean_ctor_set(x_482, 0, x_535);
lean_ctor_set(x_494, 0, x_481);
return x_494;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; 
lean_dec(x_19);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_506);
lean_ctor_set(x_538, 1, x_517);
x_539 = lean_array_push(x_516, x_538);
x_540 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_541 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_541, 0, x_490);
lean_ctor_set(x_541, 1, x_540);
x_542 = lean_array_push(x_539, x_541);
x_543 = lean_array_push(x_542, x_487);
x_544 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = lean_array_push(x_499, x_545);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_506);
lean_ctor_set(x_547, 1, x_546);
x_548 = lean_array_push(x_499, x_547);
x_549 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
x_551 = lean_array_push(x_513, x_550);
x_552 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_551);
x_554 = 1;
x_555 = lean_box(x_554);
lean_ctor_set(x_482, 1, x_555);
lean_ctor_set(x_482, 0, x_553);
lean_ctor_set(x_494, 0, x_481);
return x_494;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; 
x_556 = lean_ctor_get(x_494, 1);
lean_inc(x_556);
lean_dec(x_494);
x_557 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_490);
x_558 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_558, 0, x_490);
lean_ctor_set(x_558, 1, x_557);
x_559 = l_Array_empty___closed__1;
x_560 = lean_array_push(x_559, x_558);
x_561 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_562 = lean_array_push(x_561, x_473);
x_563 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_562);
x_565 = lean_array_push(x_559, x_564);
x_566 = l_Lean_nullKind___closed__2;
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_565);
x_568 = lean_array_push(x_560, x_567);
x_569 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_570 = lean_array_push(x_568, x_569);
x_571 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_490);
x_572 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_572, 0, x_490);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_array_push(x_570, x_572);
x_574 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_490);
x_575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_575, 0, x_490);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_array_push(x_559, x_575);
lean_inc(x_19);
x_577 = lean_array_push(x_559, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_578 = x_19;
} else {
 lean_dec_ref(x_19);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_566);
lean_ctor_set(x_579, 1, x_577);
x_580 = lean_array_push(x_576, x_579);
x_581 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_582 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_582, 0, x_490);
lean_ctor_set(x_582, 1, x_581);
x_583 = lean_array_push(x_580, x_582);
x_584 = lean_array_push(x_583, x_487);
x_585 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_584);
x_587 = lean_array_push(x_559, x_586);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_566);
lean_ctor_set(x_588, 1, x_587);
x_589 = lean_array_push(x_559, x_588);
x_590 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = lean_array_push(x_573, x_591);
x_593 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_592);
x_595 = 1;
x_596 = lean_box(x_595);
lean_ctor_set(x_482, 1, x_596);
lean_ctor_set(x_482, 0, x_594);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_481);
lean_ctor_set(x_597, 1, x_556);
return x_597;
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_598 = lean_ctor_get(x_482, 0);
lean_inc(x_598);
lean_dec(x_482);
x_599 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_483);
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_601);
lean_dec(x_5);
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
lean_dec(x_602);
x_604 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_603);
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_606 = x_604;
} else {
 lean_dec_ref(x_604);
 x_606 = lean_box(0);
}
x_607 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_600);
x_608 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_608, 0, x_600);
lean_ctor_set(x_608, 1, x_607);
x_609 = l_Array_empty___closed__1;
x_610 = lean_array_push(x_609, x_608);
x_611 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_612 = lean_array_push(x_611, x_473);
x_613 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_612);
x_615 = lean_array_push(x_609, x_614);
x_616 = l_Lean_nullKind___closed__2;
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_615);
x_618 = lean_array_push(x_610, x_617);
x_619 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_620 = lean_array_push(x_618, x_619);
x_621 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_600);
x_622 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_622, 0, x_600);
lean_ctor_set(x_622, 1, x_621);
x_623 = lean_array_push(x_620, x_622);
x_624 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_600);
x_625 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_625, 0, x_600);
lean_ctor_set(x_625, 1, x_624);
x_626 = lean_array_push(x_609, x_625);
lean_inc(x_19);
x_627 = lean_array_push(x_609, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_628 = x_19;
} else {
 lean_dec_ref(x_19);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_616);
lean_ctor_set(x_629, 1, x_627);
x_630 = lean_array_push(x_626, x_629);
x_631 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_632 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_632, 0, x_600);
lean_ctor_set(x_632, 1, x_631);
x_633 = lean_array_push(x_630, x_632);
x_634 = lean_array_push(x_633, x_598);
x_635 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_634);
x_637 = lean_array_push(x_609, x_636);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_616);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_array_push(x_609, x_638);
x_640 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_639);
x_642 = lean_array_push(x_623, x_641);
x_643 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_642);
x_645 = 1;
x_646 = lean_box(x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_646);
lean_ctor_set(x_481, 1, x_647);
if (lean_is_scalar(x_606)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_606;
}
lean_ctor_set(x_648, 0, x_481);
lean_ctor_set(x_648, 1, x_605);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_649 = lean_ctor_get(x_481, 0);
lean_inc(x_649);
lean_dec(x_481);
x_650 = lean_ctor_get(x_482, 0);
lean_inc(x_650);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_651 = x_482;
} else {
 lean_dec_ref(x_482);
 x_651 = lean_box(0);
}
x_652 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_483);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_654);
lean_dec(x_5);
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
lean_dec(x_655);
x_657 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_656);
x_658 = lean_ctor_get(x_657, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_659 = x_657;
} else {
 lean_dec_ref(x_657);
 x_659 = lean_box(0);
}
x_660 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_653);
x_661 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_661, 0, x_653);
lean_ctor_set(x_661, 1, x_660);
x_662 = l_Array_empty___closed__1;
x_663 = lean_array_push(x_662, x_661);
x_664 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_665 = lean_array_push(x_664, x_473);
x_666 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_665);
x_668 = lean_array_push(x_662, x_667);
x_669 = l_Lean_nullKind___closed__2;
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_668);
x_671 = lean_array_push(x_663, x_670);
x_672 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_673 = lean_array_push(x_671, x_672);
x_674 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_653);
x_675 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_675, 0, x_653);
lean_ctor_set(x_675, 1, x_674);
x_676 = lean_array_push(x_673, x_675);
x_677 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_653);
x_678 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_678, 0, x_653);
lean_ctor_set(x_678, 1, x_677);
x_679 = lean_array_push(x_662, x_678);
lean_inc(x_19);
x_680 = lean_array_push(x_662, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_681 = x_19;
} else {
 lean_dec_ref(x_19);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(1, 2, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_669);
lean_ctor_set(x_682, 1, x_680);
x_683 = lean_array_push(x_679, x_682);
x_684 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_685 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_685, 0, x_653);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_array_push(x_683, x_685);
x_687 = lean_array_push(x_686, x_650);
x_688 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_687);
x_690 = lean_array_push(x_662, x_689);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_669);
lean_ctor_set(x_691, 1, x_690);
x_692 = lean_array_push(x_662, x_691);
x_693 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_692);
x_695 = lean_array_push(x_676, x_694);
x_696 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_695);
x_698 = 1;
x_699 = lean_box(x_698);
if (lean_is_scalar(x_651)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_651;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_699);
x_701 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_701, 0, x_649);
lean_ctor_set(x_701, 1, x_700);
if (lean_is_scalar(x_659)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_659;
}
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_658);
return x_702;
}
}
else
{
lean_object* x_703; uint8_t x_704; 
x_703 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_704 = lean_string_dec_eq(x_234, x_703);
lean_dec(x_234);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; 
lean_dec(x_233);
lean_inc(x_5);
x_705 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
lean_dec(x_705);
x_708 = lean_unsigned_to_nat(1u);
x_709 = lean_nat_add(x_3, x_708);
lean_dec(x_3);
x_710 = l_Lean_mkHole(x_19);
lean_inc(x_706);
x_711 = l_Lean_Elab_Term_mkExplicitBinder(x_706, x_710);
x_712 = lean_array_push(x_4, x_711);
lean_inc(x_5);
x_713 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_709, x_712, x_5, x_6, x_7, x_8, x_9, x_10, x_707);
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_714, 1);
lean_inc(x_715);
x_716 = lean_ctor_get(x_713, 1);
lean_inc(x_716);
lean_dec(x_713);
x_717 = !lean_is_exclusive(x_714);
if (x_717 == 0)
{
lean_object* x_718; uint8_t x_719; 
x_718 = lean_ctor_get(x_714, 1);
lean_dec(x_718);
x_719 = !lean_is_exclusive(x_715);
if (x_719 == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; uint8_t x_728; 
x_720 = lean_ctor_get(x_715, 0);
x_721 = lean_ctor_get(x_715, 1);
lean_dec(x_721);
x_722 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_716);
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_725 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_724);
lean_dec(x_5);
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
x_727 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_726);
x_728 = !lean_is_exclusive(x_727);
if (x_728 == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_729 = lean_ctor_get(x_727, 0);
lean_dec(x_729);
x_730 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_723);
x_731 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_731, 0, x_723);
lean_ctor_set(x_731, 1, x_730);
x_732 = l_Array_empty___closed__1;
x_733 = lean_array_push(x_732, x_731);
x_734 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_735 = lean_array_push(x_734, x_706);
x_736 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_735);
x_738 = lean_array_push(x_732, x_737);
x_739 = l_Lean_nullKind___closed__2;
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_738);
x_741 = lean_array_push(x_733, x_740);
x_742 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_743 = lean_array_push(x_741, x_742);
x_744 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_723);
x_745 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_745, 0, x_723);
lean_ctor_set(x_745, 1, x_744);
x_746 = lean_array_push(x_743, x_745);
x_747 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_723);
x_748 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_748, 0, x_723);
lean_ctor_set(x_748, 1, x_747);
x_749 = lean_array_push(x_732, x_748);
lean_inc(x_19);
x_750 = lean_array_push(x_732, x_19);
x_751 = !lean_is_exclusive(x_19);
if (x_751 == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; uint8_t x_769; lean_object* x_770; 
x_752 = lean_ctor_get(x_19, 1);
lean_dec(x_752);
x_753 = lean_ctor_get(x_19, 0);
lean_dec(x_753);
lean_ctor_set(x_19, 1, x_750);
lean_ctor_set(x_19, 0, x_739);
x_754 = lean_array_push(x_749, x_19);
x_755 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_756 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_756, 0, x_723);
lean_ctor_set(x_756, 1, x_755);
x_757 = lean_array_push(x_754, x_756);
x_758 = lean_array_push(x_757, x_720);
x_759 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_758);
x_761 = lean_array_push(x_732, x_760);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_739);
lean_ctor_set(x_762, 1, x_761);
x_763 = lean_array_push(x_732, x_762);
x_764 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
x_766 = lean_array_push(x_746, x_765);
x_767 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_766);
x_769 = 1;
x_770 = lean_box(x_769);
lean_ctor_set(x_715, 1, x_770);
lean_ctor_set(x_715, 0, x_768);
lean_ctor_set(x_727, 0, x_714);
return x_727;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; lean_object* x_788; 
lean_dec(x_19);
x_771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_771, 0, x_739);
lean_ctor_set(x_771, 1, x_750);
x_772 = lean_array_push(x_749, x_771);
x_773 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_774 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_774, 0, x_723);
lean_ctor_set(x_774, 1, x_773);
x_775 = lean_array_push(x_772, x_774);
x_776 = lean_array_push(x_775, x_720);
x_777 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_776);
x_779 = lean_array_push(x_732, x_778);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_739);
lean_ctor_set(x_780, 1, x_779);
x_781 = lean_array_push(x_732, x_780);
x_782 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_781);
x_784 = lean_array_push(x_746, x_783);
x_785 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_784);
x_787 = 1;
x_788 = lean_box(x_787);
lean_ctor_set(x_715, 1, x_788);
lean_ctor_set(x_715, 0, x_786);
lean_ctor_set(x_727, 0, x_714);
return x_727;
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint8_t x_828; lean_object* x_829; lean_object* x_830; 
x_789 = lean_ctor_get(x_727, 1);
lean_inc(x_789);
lean_dec(x_727);
x_790 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_723);
x_791 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_791, 0, x_723);
lean_ctor_set(x_791, 1, x_790);
x_792 = l_Array_empty___closed__1;
x_793 = lean_array_push(x_792, x_791);
x_794 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_795 = lean_array_push(x_794, x_706);
x_796 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_795);
x_798 = lean_array_push(x_792, x_797);
x_799 = l_Lean_nullKind___closed__2;
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_798);
x_801 = lean_array_push(x_793, x_800);
x_802 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_803 = lean_array_push(x_801, x_802);
x_804 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_723);
x_805 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_805, 0, x_723);
lean_ctor_set(x_805, 1, x_804);
x_806 = lean_array_push(x_803, x_805);
x_807 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_723);
x_808 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_808, 0, x_723);
lean_ctor_set(x_808, 1, x_807);
x_809 = lean_array_push(x_792, x_808);
lean_inc(x_19);
x_810 = lean_array_push(x_792, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_811 = x_19;
} else {
 lean_dec_ref(x_19);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_799);
lean_ctor_set(x_812, 1, x_810);
x_813 = lean_array_push(x_809, x_812);
x_814 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_815 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_815, 0, x_723);
lean_ctor_set(x_815, 1, x_814);
x_816 = lean_array_push(x_813, x_815);
x_817 = lean_array_push(x_816, x_720);
x_818 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_817);
x_820 = lean_array_push(x_792, x_819);
x_821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_821, 0, x_799);
lean_ctor_set(x_821, 1, x_820);
x_822 = lean_array_push(x_792, x_821);
x_823 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_822);
x_825 = lean_array_push(x_806, x_824);
x_826 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_825);
x_828 = 1;
x_829 = lean_box(x_828);
lean_ctor_set(x_715, 1, x_829);
lean_ctor_set(x_715, 0, x_827);
x_830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_830, 0, x_714);
lean_ctor_set(x_830, 1, x_789);
return x_830;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; uint8_t x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_831 = lean_ctor_get(x_715, 0);
lean_inc(x_831);
lean_dec(x_715);
x_832 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_716);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_834);
lean_dec(x_5);
x_836 = lean_ctor_get(x_835, 1);
lean_inc(x_836);
lean_dec(x_835);
x_837 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_836);
x_838 = lean_ctor_get(x_837, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_839 = x_837;
} else {
 lean_dec_ref(x_837);
 x_839 = lean_box(0);
}
x_840 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_833);
x_841 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_841, 0, x_833);
lean_ctor_set(x_841, 1, x_840);
x_842 = l_Array_empty___closed__1;
x_843 = lean_array_push(x_842, x_841);
x_844 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_845 = lean_array_push(x_844, x_706);
x_846 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_845);
x_848 = lean_array_push(x_842, x_847);
x_849 = l_Lean_nullKind___closed__2;
x_850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_848);
x_851 = lean_array_push(x_843, x_850);
x_852 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_853 = lean_array_push(x_851, x_852);
x_854 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_833);
x_855 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_855, 0, x_833);
lean_ctor_set(x_855, 1, x_854);
x_856 = lean_array_push(x_853, x_855);
x_857 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_833);
x_858 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_858, 0, x_833);
lean_ctor_set(x_858, 1, x_857);
x_859 = lean_array_push(x_842, x_858);
lean_inc(x_19);
x_860 = lean_array_push(x_842, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_861 = x_19;
} else {
 lean_dec_ref(x_19);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_849);
lean_ctor_set(x_862, 1, x_860);
x_863 = lean_array_push(x_859, x_862);
x_864 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_865 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_865, 0, x_833);
lean_ctor_set(x_865, 1, x_864);
x_866 = lean_array_push(x_863, x_865);
x_867 = lean_array_push(x_866, x_831);
x_868 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_867);
x_870 = lean_array_push(x_842, x_869);
x_871 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_871, 0, x_849);
lean_ctor_set(x_871, 1, x_870);
x_872 = lean_array_push(x_842, x_871);
x_873 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_874, 0, x_873);
lean_ctor_set(x_874, 1, x_872);
x_875 = lean_array_push(x_856, x_874);
x_876 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_875);
x_878 = 1;
x_879 = lean_box(x_878);
x_880 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_880, 0, x_877);
lean_ctor_set(x_880, 1, x_879);
lean_ctor_set(x_714, 1, x_880);
if (lean_is_scalar(x_839)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_839;
}
lean_ctor_set(x_881, 0, x_714);
lean_ctor_set(x_881, 1, x_838);
return x_881;
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; uint8_t x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_882 = lean_ctor_get(x_714, 0);
lean_inc(x_882);
lean_dec(x_714);
x_883 = lean_ctor_get(x_715, 0);
lean_inc(x_883);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_884 = x_715;
} else {
 lean_dec_ref(x_715);
 x_884 = lean_box(0);
}
x_885 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_716);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_887);
lean_dec(x_5);
x_889 = lean_ctor_get(x_888, 1);
lean_inc(x_889);
lean_dec(x_888);
x_890 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_889);
x_891 = lean_ctor_get(x_890, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_892 = x_890;
} else {
 lean_dec_ref(x_890);
 x_892 = lean_box(0);
}
x_893 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_886);
x_894 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_894, 0, x_886);
lean_ctor_set(x_894, 1, x_893);
x_895 = l_Array_empty___closed__1;
x_896 = lean_array_push(x_895, x_894);
x_897 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_898 = lean_array_push(x_897, x_706);
x_899 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_898);
x_901 = lean_array_push(x_895, x_900);
x_902 = l_Lean_nullKind___closed__2;
x_903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_901);
x_904 = lean_array_push(x_896, x_903);
x_905 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_906 = lean_array_push(x_904, x_905);
x_907 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_886);
x_908 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_908, 0, x_886);
lean_ctor_set(x_908, 1, x_907);
x_909 = lean_array_push(x_906, x_908);
x_910 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_886);
x_911 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_911, 0, x_886);
lean_ctor_set(x_911, 1, x_910);
x_912 = lean_array_push(x_895, x_911);
lean_inc(x_19);
x_913 = lean_array_push(x_895, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_914 = x_19;
} else {
 lean_dec_ref(x_19);
 x_914 = lean_box(0);
}
if (lean_is_scalar(x_914)) {
 x_915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_915 = x_914;
}
lean_ctor_set(x_915, 0, x_902);
lean_ctor_set(x_915, 1, x_913);
x_916 = lean_array_push(x_912, x_915);
x_917 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_918 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_918, 0, x_886);
lean_ctor_set(x_918, 1, x_917);
x_919 = lean_array_push(x_916, x_918);
x_920 = lean_array_push(x_919, x_883);
x_921 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_922, 1, x_920);
x_923 = lean_array_push(x_895, x_922);
x_924 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_924, 0, x_902);
lean_ctor_set(x_924, 1, x_923);
x_925 = lean_array_push(x_895, x_924);
x_926 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_927 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_927, 0, x_926);
lean_ctor_set(x_927, 1, x_925);
x_928 = lean_array_push(x_909, x_927);
x_929 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_930 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_928);
x_931 = 1;
x_932 = lean_box(x_931);
if (lean_is_scalar(x_884)) {
 x_933 = lean_alloc_ctor(0, 2, 0);
} else {
 x_933 = x_884;
}
lean_ctor_set(x_933, 0, x_930);
lean_ctor_set(x_933, 1, x_932);
x_934 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_934, 0, x_882);
lean_ctor_set(x_934, 1, x_933);
if (lean_is_scalar(x_892)) {
 x_935 = lean_alloc_ctor(0, 2, 0);
} else {
 x_935 = x_892;
}
lean_ctor_set(x_935, 0, x_934);
lean_ctor_set(x_935, 1, x_891);
return x_935;
}
}
else
{
lean_object* x_936; uint8_t x_937; 
x_936 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___lambda__2___closed__2;
x_937 = lean_string_dec_eq(x_233, x_936);
if (x_937 == 0)
{
lean_object* x_938; uint8_t x_939; 
x_938 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__2;
x_939 = lean_string_dec_eq(x_233, x_938);
if (x_939 == 0)
{
lean_object* x_940; uint8_t x_941; 
x_940 = l_Array_forInUnsafe_loop___at_myMacro____x40_Init_NotationExtra___hyg_5659____spec__3___closed__1;
x_941 = lean_string_dec_eq(x_233, x_940);
if (x_941 == 0)
{
lean_object* x_942; uint8_t x_943; 
x_942 = l_Lean_expandExplicitBindersAux_loop___closed__1;
x_943 = lean_string_dec_eq(x_233, x_942);
if (x_943 == 0)
{
lean_object* x_944; uint8_t x_945; 
x_944 = l_myMacro____x40_Init_Notation___hyg_14520____closed__12;
x_945 = lean_string_dec_eq(x_233, x_944);
if (x_945 == 0)
{
lean_object* x_946; uint8_t x_947; 
x_946 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
x_947 = lean_string_dec_eq(x_233, x_946);
lean_dec(x_233);
if (x_947 == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint8_t x_960; 
lean_inc(x_5);
x_948 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_unsigned_to_nat(1u);
x_952 = lean_nat_add(x_3, x_951);
lean_dec(x_3);
x_953 = l_Lean_mkHole(x_19);
lean_inc(x_949);
x_954 = l_Lean_Elab_Term_mkExplicitBinder(x_949, x_953);
x_955 = lean_array_push(x_4, x_954);
lean_inc(x_5);
x_956 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_952, x_955, x_5, x_6, x_7, x_8, x_9, x_10, x_950);
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_957, 1);
lean_inc(x_958);
x_959 = lean_ctor_get(x_956, 1);
lean_inc(x_959);
lean_dec(x_956);
x_960 = !lean_is_exclusive(x_957);
if (x_960 == 0)
{
lean_object* x_961; uint8_t x_962; 
x_961 = lean_ctor_get(x_957, 1);
lean_dec(x_961);
x_962 = !lean_is_exclusive(x_958);
if (x_962 == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; uint8_t x_971; 
x_963 = lean_ctor_get(x_958, 0);
x_964 = lean_ctor_get(x_958, 1);
lean_dec(x_964);
x_965 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_959);
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_967);
lean_dec(x_5);
x_969 = lean_ctor_get(x_968, 1);
lean_inc(x_969);
lean_dec(x_968);
x_970 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_969);
x_971 = !lean_is_exclusive(x_970);
if (x_971 == 0)
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; uint8_t x_994; 
x_972 = lean_ctor_get(x_970, 0);
lean_dec(x_972);
x_973 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_966);
x_974 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_974, 0, x_966);
lean_ctor_set(x_974, 1, x_973);
x_975 = l_Array_empty___closed__1;
x_976 = lean_array_push(x_975, x_974);
x_977 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_978 = lean_array_push(x_977, x_949);
x_979 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_978);
x_981 = lean_array_push(x_975, x_980);
x_982 = l_Lean_nullKind___closed__2;
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_981);
x_984 = lean_array_push(x_976, x_983);
x_985 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_986 = lean_array_push(x_984, x_985);
x_987 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_966);
x_988 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_988, 0, x_966);
lean_ctor_set(x_988, 1, x_987);
x_989 = lean_array_push(x_986, x_988);
x_990 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_966);
x_991 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_991, 0, x_966);
lean_ctor_set(x_991, 1, x_990);
x_992 = lean_array_push(x_975, x_991);
lean_inc(x_19);
x_993 = lean_array_push(x_975, x_19);
x_994 = !lean_is_exclusive(x_19);
if (x_994 == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; uint8_t x_1012; lean_object* x_1013; 
x_995 = lean_ctor_get(x_19, 1);
lean_dec(x_995);
x_996 = lean_ctor_get(x_19, 0);
lean_dec(x_996);
lean_ctor_set(x_19, 1, x_993);
lean_ctor_set(x_19, 0, x_982);
x_997 = lean_array_push(x_992, x_19);
x_998 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_999 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_999, 0, x_966);
lean_ctor_set(x_999, 1, x_998);
x_1000 = lean_array_push(x_997, x_999);
x_1001 = lean_array_push(x_1000, x_963);
x_1002 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1003 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1003, 0, x_1002);
lean_ctor_set(x_1003, 1, x_1001);
x_1004 = lean_array_push(x_975, x_1003);
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_982);
lean_ctor_set(x_1005, 1, x_1004);
x_1006 = lean_array_push(x_975, x_1005);
x_1007 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = lean_array_push(x_989, x_1008);
x_1010 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_1010);
lean_ctor_set(x_1011, 1, x_1009);
x_1012 = 1;
x_1013 = lean_box(x_1012);
lean_ctor_set(x_958, 1, x_1013);
lean_ctor_set(x_958, 0, x_1011);
lean_ctor_set(x_970, 0, x_957);
return x_970;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; uint8_t x_1030; lean_object* x_1031; 
lean_dec(x_19);
x_1014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1014, 0, x_982);
lean_ctor_set(x_1014, 1, x_993);
x_1015 = lean_array_push(x_992, x_1014);
x_1016 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1017 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1017, 0, x_966);
lean_ctor_set(x_1017, 1, x_1016);
x_1018 = lean_array_push(x_1015, x_1017);
x_1019 = lean_array_push(x_1018, x_963);
x_1020 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1020);
lean_ctor_set(x_1021, 1, x_1019);
x_1022 = lean_array_push(x_975, x_1021);
x_1023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1023, 0, x_982);
lean_ctor_set(x_1023, 1, x_1022);
x_1024 = lean_array_push(x_975, x_1023);
x_1025 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1026, 0, x_1025);
lean_ctor_set(x_1026, 1, x_1024);
x_1027 = lean_array_push(x_989, x_1026);
x_1028 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1029 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1029, 0, x_1028);
lean_ctor_set(x_1029, 1, x_1027);
x_1030 = 1;
x_1031 = lean_box(x_1030);
lean_ctor_set(x_958, 1, x_1031);
lean_ctor_set(x_958, 0, x_1029);
lean_ctor_set(x_970, 0, x_957);
return x_970;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1032 = lean_ctor_get(x_970, 1);
lean_inc(x_1032);
lean_dec(x_970);
x_1033 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_966);
x_1034 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1034, 0, x_966);
lean_ctor_set(x_1034, 1, x_1033);
x_1035 = l_Array_empty___closed__1;
x_1036 = lean_array_push(x_1035, x_1034);
x_1037 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1038 = lean_array_push(x_1037, x_949);
x_1039 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1040 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1040, 0, x_1039);
lean_ctor_set(x_1040, 1, x_1038);
x_1041 = lean_array_push(x_1035, x_1040);
x_1042 = l_Lean_nullKind___closed__2;
x_1043 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_1041);
x_1044 = lean_array_push(x_1036, x_1043);
x_1045 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1046 = lean_array_push(x_1044, x_1045);
x_1047 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_966);
x_1048 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1048, 0, x_966);
lean_ctor_set(x_1048, 1, x_1047);
x_1049 = lean_array_push(x_1046, x_1048);
x_1050 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_966);
x_1051 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1051, 0, x_966);
lean_ctor_set(x_1051, 1, x_1050);
x_1052 = lean_array_push(x_1035, x_1051);
lean_inc(x_19);
x_1053 = lean_array_push(x_1035, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1054 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1042);
lean_ctor_set(x_1055, 1, x_1053);
x_1056 = lean_array_push(x_1052, x_1055);
x_1057 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1058 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1058, 0, x_966);
lean_ctor_set(x_1058, 1, x_1057);
x_1059 = lean_array_push(x_1056, x_1058);
x_1060 = lean_array_push(x_1059, x_963);
x_1061 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1062 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_1060);
x_1063 = lean_array_push(x_1035, x_1062);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1042);
lean_ctor_set(x_1064, 1, x_1063);
x_1065 = lean_array_push(x_1035, x_1064);
x_1066 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_1065);
x_1068 = lean_array_push(x_1049, x_1067);
x_1069 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1070 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1068);
x_1071 = 1;
x_1072 = lean_box(x_1071);
lean_ctor_set(x_958, 1, x_1072);
lean_ctor_set(x_958, 0, x_1070);
x_1073 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1073, 0, x_957);
lean_ctor_set(x_1073, 1, x_1032);
return x_1073;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; uint8_t x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1074 = lean_ctor_get(x_958, 0);
lean_inc(x_1074);
lean_dec(x_958);
x_1075 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_959);
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1075, 1);
lean_inc(x_1077);
lean_dec(x_1075);
x_1078 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1077);
lean_dec(x_5);
x_1079 = lean_ctor_get(x_1078, 1);
lean_inc(x_1079);
lean_dec(x_1078);
x_1080 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1079);
x_1081 = lean_ctor_get(x_1080, 1);
lean_inc(x_1081);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 lean_ctor_release(x_1080, 1);
 x_1082 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1082 = lean_box(0);
}
x_1083 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1076);
x_1084 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1084, 0, x_1076);
lean_ctor_set(x_1084, 1, x_1083);
x_1085 = l_Array_empty___closed__1;
x_1086 = lean_array_push(x_1085, x_1084);
x_1087 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1088 = lean_array_push(x_1087, x_949);
x_1089 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1090, 0, x_1089);
lean_ctor_set(x_1090, 1, x_1088);
x_1091 = lean_array_push(x_1085, x_1090);
x_1092 = l_Lean_nullKind___closed__2;
x_1093 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1093, 0, x_1092);
lean_ctor_set(x_1093, 1, x_1091);
x_1094 = lean_array_push(x_1086, x_1093);
x_1095 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1096 = lean_array_push(x_1094, x_1095);
x_1097 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1076);
x_1098 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1098, 0, x_1076);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = lean_array_push(x_1096, x_1098);
x_1100 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1076);
x_1101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1101, 0, x_1076);
lean_ctor_set(x_1101, 1, x_1100);
x_1102 = lean_array_push(x_1085, x_1101);
lean_inc(x_19);
x_1103 = lean_array_push(x_1085, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1104 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1092);
lean_ctor_set(x_1105, 1, x_1103);
x_1106 = lean_array_push(x_1102, x_1105);
x_1107 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1108, 0, x_1076);
lean_ctor_set(x_1108, 1, x_1107);
x_1109 = lean_array_push(x_1106, x_1108);
x_1110 = lean_array_push(x_1109, x_1074);
x_1111 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_1110);
x_1113 = lean_array_push(x_1085, x_1112);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1092);
lean_ctor_set(x_1114, 1, x_1113);
x_1115 = lean_array_push(x_1085, x_1114);
x_1116 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1115);
x_1118 = lean_array_push(x_1099, x_1117);
x_1119 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1120, 1, x_1118);
x_1121 = 1;
x_1122 = lean_box(x_1121);
x_1123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1123, 0, x_1120);
lean_ctor_set(x_1123, 1, x_1122);
lean_ctor_set(x_957, 1, x_1123);
if (lean_is_scalar(x_1082)) {
 x_1124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1124 = x_1082;
}
lean_ctor_set(x_1124, 0, x_957);
lean_ctor_set(x_1124, 1, x_1081);
return x_1124;
}
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; uint8_t x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1125 = lean_ctor_get(x_957, 0);
lean_inc(x_1125);
lean_dec(x_957);
x_1126 = lean_ctor_get(x_958, 0);
lean_inc(x_1126);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_1127 = x_958;
} else {
 lean_dec_ref(x_958);
 x_1127 = lean_box(0);
}
x_1128 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_959);
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
lean_dec(x_1128);
x_1131 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1130);
lean_dec(x_5);
x_1132 = lean_ctor_get(x_1131, 1);
lean_inc(x_1132);
lean_dec(x_1131);
x_1133 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1132);
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
x_1136 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1129);
x_1137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1137, 0, x_1129);
lean_ctor_set(x_1137, 1, x_1136);
x_1138 = l_Array_empty___closed__1;
x_1139 = lean_array_push(x_1138, x_1137);
x_1140 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1141 = lean_array_push(x_1140, x_949);
x_1142 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1143, 0, x_1142);
lean_ctor_set(x_1143, 1, x_1141);
x_1144 = lean_array_push(x_1138, x_1143);
x_1145 = l_Lean_nullKind___closed__2;
x_1146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1146, 0, x_1145);
lean_ctor_set(x_1146, 1, x_1144);
x_1147 = lean_array_push(x_1139, x_1146);
x_1148 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1149 = lean_array_push(x_1147, x_1148);
x_1150 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1129);
x_1151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1151, 0, x_1129);
lean_ctor_set(x_1151, 1, x_1150);
x_1152 = lean_array_push(x_1149, x_1151);
x_1153 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1129);
x_1154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1154, 0, x_1129);
lean_ctor_set(x_1154, 1, x_1153);
x_1155 = lean_array_push(x_1138, x_1154);
lean_inc(x_19);
x_1156 = lean_array_push(x_1138, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1157 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1145);
lean_ctor_set(x_1158, 1, x_1156);
x_1159 = lean_array_push(x_1155, x_1158);
x_1160 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1161, 0, x_1129);
lean_ctor_set(x_1161, 1, x_1160);
x_1162 = lean_array_push(x_1159, x_1161);
x_1163 = lean_array_push(x_1162, x_1126);
x_1164 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1165, 0, x_1164);
lean_ctor_set(x_1165, 1, x_1163);
x_1166 = lean_array_push(x_1138, x_1165);
x_1167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1167, 0, x_1145);
lean_ctor_set(x_1167, 1, x_1166);
x_1168 = lean_array_push(x_1138, x_1167);
x_1169 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1170, 0, x_1169);
lean_ctor_set(x_1170, 1, x_1168);
x_1171 = lean_array_push(x_1152, x_1170);
x_1172 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1172);
lean_ctor_set(x_1173, 1, x_1171);
x_1174 = 1;
x_1175 = lean_box(x_1174);
if (lean_is_scalar(x_1127)) {
 x_1176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1176 = x_1127;
}
lean_ctor_set(x_1176, 0, x_1173);
lean_ctor_set(x_1176, 1, x_1175);
x_1177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1177, 0, x_1125);
lean_ctor_set(x_1177, 1, x_1176);
if (lean_is_scalar(x_1135)) {
 x_1178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1178 = x_1135;
}
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1134);
return x_1178;
}
}
else
{
lean_object* x_1179; lean_object* x_1180; uint8_t x_1181; 
x_1179 = lean_unsigned_to_nat(1u);
x_1180 = l_Lean_Syntax_getArg(x_19, x_1179);
x_1181 = l_Lean_Syntax_isNone(x_1180);
if (x_1181 == 0)
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; uint8_t x_1185; 
x_1182 = lean_unsigned_to_nat(0u);
x_1183 = l_Lean_Syntax_getArg(x_1180, x_1182);
x_1184 = l_Lean_Syntax_getArg(x_1180, x_1179);
lean_dec(x_1180);
x_1185 = l_Lean_Syntax_isNone(x_1184);
if (x_1185 == 0)
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; 
x_1186 = l_Lean_Syntax_getArg(x_1184, x_1182);
lean_dec(x_1184);
lean_inc(x_1186);
x_1187 = l_Lean_Syntax_getKind(x_1186);
x_1188 = l_myMacro____x40_Init_Notation___hyg_15440____closed__8;
x_1189 = lean_name_eq(x_1187, x_1188);
lean_dec(x_1187);
if (x_1189 == 0)
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; uint8_t x_1201; 
lean_dec(x_1186);
lean_dec(x_1183);
lean_inc(x_5);
x_1190 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1190, 1);
lean_inc(x_1192);
lean_dec(x_1190);
x_1193 = lean_nat_add(x_3, x_1179);
lean_dec(x_3);
x_1194 = l_Lean_mkHole(x_19);
lean_inc(x_1191);
x_1195 = l_Lean_Elab_Term_mkExplicitBinder(x_1191, x_1194);
x_1196 = lean_array_push(x_4, x_1195);
lean_inc(x_5);
x_1197 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1193, x_1196, x_5, x_6, x_7, x_8, x_9, x_10, x_1192);
x_1198 = lean_ctor_get(x_1197, 0);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1198, 1);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1197, 1);
lean_inc(x_1200);
lean_dec(x_1197);
x_1201 = !lean_is_exclusive(x_1198);
if (x_1201 == 0)
{
lean_object* x_1202; uint8_t x_1203; 
x_1202 = lean_ctor_get(x_1198, 1);
lean_dec(x_1202);
x_1203 = !lean_is_exclusive(x_1199);
if (x_1203 == 0)
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; uint8_t x_1212; 
x_1204 = lean_ctor_get(x_1199, 0);
x_1205 = lean_ctor_get(x_1199, 1);
lean_dec(x_1205);
x_1206 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1200);
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1208);
lean_dec(x_5);
x_1210 = lean_ctor_get(x_1209, 1);
lean_inc(x_1210);
lean_dec(x_1209);
x_1211 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1210);
x_1212 = !lean_is_exclusive(x_1211);
if (x_1212 == 0)
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; uint8_t x_1235; 
x_1213 = lean_ctor_get(x_1211, 0);
lean_dec(x_1213);
x_1214 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1207);
x_1215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1215, 0, x_1207);
lean_ctor_set(x_1215, 1, x_1214);
x_1216 = l_Array_empty___closed__1;
x_1217 = lean_array_push(x_1216, x_1215);
x_1218 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1219 = lean_array_push(x_1218, x_1191);
x_1220 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = lean_array_push(x_1216, x_1221);
x_1223 = l_Lean_nullKind___closed__2;
x_1224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1224, 0, x_1223);
lean_ctor_set(x_1224, 1, x_1222);
x_1225 = lean_array_push(x_1217, x_1224);
x_1226 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1227 = lean_array_push(x_1225, x_1226);
x_1228 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1207);
x_1229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1229, 0, x_1207);
lean_ctor_set(x_1229, 1, x_1228);
x_1230 = lean_array_push(x_1227, x_1229);
x_1231 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1207);
x_1232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1232, 0, x_1207);
lean_ctor_set(x_1232, 1, x_1231);
x_1233 = lean_array_push(x_1216, x_1232);
lean_inc(x_19);
x_1234 = lean_array_push(x_1216, x_19);
x_1235 = !lean_is_exclusive(x_19);
if (x_1235 == 0)
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; uint8_t x_1253; lean_object* x_1254; 
x_1236 = lean_ctor_get(x_19, 1);
lean_dec(x_1236);
x_1237 = lean_ctor_get(x_19, 0);
lean_dec(x_1237);
lean_ctor_set(x_19, 1, x_1234);
lean_ctor_set(x_19, 0, x_1223);
x_1238 = lean_array_push(x_1233, x_19);
x_1239 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1240 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1240, 0, x_1207);
lean_ctor_set(x_1240, 1, x_1239);
x_1241 = lean_array_push(x_1238, x_1240);
x_1242 = lean_array_push(x_1241, x_1204);
x_1243 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1244, 0, x_1243);
lean_ctor_set(x_1244, 1, x_1242);
x_1245 = lean_array_push(x_1216, x_1244);
x_1246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1246, 0, x_1223);
lean_ctor_set(x_1246, 1, x_1245);
x_1247 = lean_array_push(x_1216, x_1246);
x_1248 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1249, 0, x_1248);
lean_ctor_set(x_1249, 1, x_1247);
x_1250 = lean_array_push(x_1230, x_1249);
x_1251 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1252, 0, x_1251);
lean_ctor_set(x_1252, 1, x_1250);
x_1253 = 1;
x_1254 = lean_box(x_1253);
lean_ctor_set(x_1199, 1, x_1254);
lean_ctor_set(x_1199, 0, x_1252);
lean_ctor_set(x_1211, 0, x_1198);
return x_1211;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; uint8_t x_1271; lean_object* x_1272; 
lean_dec(x_19);
x_1255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1255, 0, x_1223);
lean_ctor_set(x_1255, 1, x_1234);
x_1256 = lean_array_push(x_1233, x_1255);
x_1257 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1258, 0, x_1207);
lean_ctor_set(x_1258, 1, x_1257);
x_1259 = lean_array_push(x_1256, x_1258);
x_1260 = lean_array_push(x_1259, x_1204);
x_1261 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1262, 0, x_1261);
lean_ctor_set(x_1262, 1, x_1260);
x_1263 = lean_array_push(x_1216, x_1262);
x_1264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1264, 0, x_1223);
lean_ctor_set(x_1264, 1, x_1263);
x_1265 = lean_array_push(x_1216, x_1264);
x_1266 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1267, 0, x_1266);
lean_ctor_set(x_1267, 1, x_1265);
x_1268 = lean_array_push(x_1230, x_1267);
x_1269 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1269);
lean_ctor_set(x_1270, 1, x_1268);
x_1271 = 1;
x_1272 = lean_box(x_1271);
lean_ctor_set(x_1199, 1, x_1272);
lean_ctor_set(x_1199, 0, x_1270);
lean_ctor_set(x_1211, 0, x_1198);
return x_1211;
}
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1273 = lean_ctor_get(x_1211, 1);
lean_inc(x_1273);
lean_dec(x_1211);
x_1274 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1207);
x_1275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1275, 0, x_1207);
lean_ctor_set(x_1275, 1, x_1274);
x_1276 = l_Array_empty___closed__1;
x_1277 = lean_array_push(x_1276, x_1275);
x_1278 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1279 = lean_array_push(x_1278, x_1191);
x_1280 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1281, 0, x_1280);
lean_ctor_set(x_1281, 1, x_1279);
x_1282 = lean_array_push(x_1276, x_1281);
x_1283 = l_Lean_nullKind___closed__2;
x_1284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1284, 0, x_1283);
lean_ctor_set(x_1284, 1, x_1282);
x_1285 = lean_array_push(x_1277, x_1284);
x_1286 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1287 = lean_array_push(x_1285, x_1286);
x_1288 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1207);
x_1289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1289, 0, x_1207);
lean_ctor_set(x_1289, 1, x_1288);
x_1290 = lean_array_push(x_1287, x_1289);
x_1291 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1207);
x_1292 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1292, 0, x_1207);
lean_ctor_set(x_1292, 1, x_1291);
x_1293 = lean_array_push(x_1276, x_1292);
lean_inc(x_19);
x_1294 = lean_array_push(x_1276, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1295 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_1283);
lean_ctor_set(x_1296, 1, x_1294);
x_1297 = lean_array_push(x_1293, x_1296);
x_1298 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1299 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1299, 0, x_1207);
lean_ctor_set(x_1299, 1, x_1298);
x_1300 = lean_array_push(x_1297, x_1299);
x_1301 = lean_array_push(x_1300, x_1204);
x_1302 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1302);
lean_ctor_set(x_1303, 1, x_1301);
x_1304 = lean_array_push(x_1276, x_1303);
x_1305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1305, 0, x_1283);
lean_ctor_set(x_1305, 1, x_1304);
x_1306 = lean_array_push(x_1276, x_1305);
x_1307 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1308, 0, x_1307);
lean_ctor_set(x_1308, 1, x_1306);
x_1309 = lean_array_push(x_1290, x_1308);
x_1310 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1311, 0, x_1310);
lean_ctor_set(x_1311, 1, x_1309);
x_1312 = 1;
x_1313 = lean_box(x_1312);
lean_ctor_set(x_1199, 1, x_1313);
lean_ctor_set(x_1199, 0, x_1311);
x_1314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1314, 0, x_1198);
lean_ctor_set(x_1314, 1, x_1273);
return x_1314;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; uint8_t x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1315 = lean_ctor_get(x_1199, 0);
lean_inc(x_1315);
lean_dec(x_1199);
x_1316 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1200);
x_1317 = lean_ctor_get(x_1316, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1316, 1);
lean_inc(x_1318);
lean_dec(x_1316);
x_1319 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1318);
lean_dec(x_5);
x_1320 = lean_ctor_get(x_1319, 1);
lean_inc(x_1320);
lean_dec(x_1319);
x_1321 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1320);
x_1322 = lean_ctor_get(x_1321, 1);
lean_inc(x_1322);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1323 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1323 = lean_box(0);
}
x_1324 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1317);
x_1325 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1325, 0, x_1317);
lean_ctor_set(x_1325, 1, x_1324);
x_1326 = l_Array_empty___closed__1;
x_1327 = lean_array_push(x_1326, x_1325);
x_1328 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1329 = lean_array_push(x_1328, x_1191);
x_1330 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1331, 0, x_1330);
lean_ctor_set(x_1331, 1, x_1329);
x_1332 = lean_array_push(x_1326, x_1331);
x_1333 = l_Lean_nullKind___closed__2;
x_1334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1334, 0, x_1333);
lean_ctor_set(x_1334, 1, x_1332);
x_1335 = lean_array_push(x_1327, x_1334);
x_1336 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1337 = lean_array_push(x_1335, x_1336);
x_1338 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1317);
x_1339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1339, 0, x_1317);
lean_ctor_set(x_1339, 1, x_1338);
x_1340 = lean_array_push(x_1337, x_1339);
x_1341 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1317);
x_1342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1342, 0, x_1317);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = lean_array_push(x_1326, x_1342);
lean_inc(x_19);
x_1344 = lean_array_push(x_1326, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1345 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1345 = lean_box(0);
}
if (lean_is_scalar(x_1345)) {
 x_1346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1346 = x_1345;
}
lean_ctor_set(x_1346, 0, x_1333);
lean_ctor_set(x_1346, 1, x_1344);
x_1347 = lean_array_push(x_1343, x_1346);
x_1348 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1349, 0, x_1317);
lean_ctor_set(x_1349, 1, x_1348);
x_1350 = lean_array_push(x_1347, x_1349);
x_1351 = lean_array_push(x_1350, x_1315);
x_1352 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1353, 0, x_1352);
lean_ctor_set(x_1353, 1, x_1351);
x_1354 = lean_array_push(x_1326, x_1353);
x_1355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1355, 0, x_1333);
lean_ctor_set(x_1355, 1, x_1354);
x_1356 = lean_array_push(x_1326, x_1355);
x_1357 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1358, 0, x_1357);
lean_ctor_set(x_1358, 1, x_1356);
x_1359 = lean_array_push(x_1340, x_1358);
x_1360 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1361, 0, x_1360);
lean_ctor_set(x_1361, 1, x_1359);
x_1362 = 1;
x_1363 = lean_box(x_1362);
x_1364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1364, 0, x_1361);
lean_ctor_set(x_1364, 1, x_1363);
lean_ctor_set(x_1198, 1, x_1364);
if (lean_is_scalar(x_1323)) {
 x_1365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1365 = x_1323;
}
lean_ctor_set(x_1365, 0, x_1198);
lean_ctor_set(x_1365, 1, x_1322);
return x_1365;
}
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; uint8_t x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1366 = lean_ctor_get(x_1198, 0);
lean_inc(x_1366);
lean_dec(x_1198);
x_1367 = lean_ctor_get(x_1199, 0);
lean_inc(x_1367);
if (lean_is_exclusive(x_1199)) {
 lean_ctor_release(x_1199, 0);
 lean_ctor_release(x_1199, 1);
 x_1368 = x_1199;
} else {
 lean_dec_ref(x_1199);
 x_1368 = lean_box(0);
}
x_1369 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1200);
x_1370 = lean_ctor_get(x_1369, 0);
lean_inc(x_1370);
x_1371 = lean_ctor_get(x_1369, 1);
lean_inc(x_1371);
lean_dec(x_1369);
x_1372 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1371);
lean_dec(x_5);
x_1373 = lean_ctor_get(x_1372, 1);
lean_inc(x_1373);
lean_dec(x_1372);
x_1374 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1373);
x_1375 = lean_ctor_get(x_1374, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1376 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1376 = lean_box(0);
}
x_1377 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1370);
x_1378 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1378, 0, x_1370);
lean_ctor_set(x_1378, 1, x_1377);
x_1379 = l_Array_empty___closed__1;
x_1380 = lean_array_push(x_1379, x_1378);
x_1381 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1382 = lean_array_push(x_1381, x_1191);
x_1383 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1384, 0, x_1383);
lean_ctor_set(x_1384, 1, x_1382);
x_1385 = lean_array_push(x_1379, x_1384);
x_1386 = l_Lean_nullKind___closed__2;
x_1387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1387, 0, x_1386);
lean_ctor_set(x_1387, 1, x_1385);
x_1388 = lean_array_push(x_1380, x_1387);
x_1389 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1390 = lean_array_push(x_1388, x_1389);
x_1391 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1370);
x_1392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1392, 0, x_1370);
lean_ctor_set(x_1392, 1, x_1391);
x_1393 = lean_array_push(x_1390, x_1392);
x_1394 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1370);
x_1395 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1395, 0, x_1370);
lean_ctor_set(x_1395, 1, x_1394);
x_1396 = lean_array_push(x_1379, x_1395);
lean_inc(x_19);
x_1397 = lean_array_push(x_1379, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1398 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1398 = lean_box(0);
}
if (lean_is_scalar(x_1398)) {
 x_1399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1399 = x_1398;
}
lean_ctor_set(x_1399, 0, x_1386);
lean_ctor_set(x_1399, 1, x_1397);
x_1400 = lean_array_push(x_1396, x_1399);
x_1401 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1402 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1402, 0, x_1370);
lean_ctor_set(x_1402, 1, x_1401);
x_1403 = lean_array_push(x_1400, x_1402);
x_1404 = lean_array_push(x_1403, x_1367);
x_1405 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1406, 0, x_1405);
lean_ctor_set(x_1406, 1, x_1404);
x_1407 = lean_array_push(x_1379, x_1406);
x_1408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1408, 0, x_1386);
lean_ctor_set(x_1408, 1, x_1407);
x_1409 = lean_array_push(x_1379, x_1408);
x_1410 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1411, 0, x_1410);
lean_ctor_set(x_1411, 1, x_1409);
x_1412 = lean_array_push(x_1393, x_1411);
x_1413 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1414, 0, x_1413);
lean_ctor_set(x_1414, 1, x_1412);
x_1415 = 1;
x_1416 = lean_box(x_1415);
if (lean_is_scalar(x_1368)) {
 x_1417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1417 = x_1368;
}
lean_ctor_set(x_1417, 0, x_1414);
lean_ctor_set(x_1417, 1, x_1416);
x_1418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1418, 0, x_1366);
lean_ctor_set(x_1418, 1, x_1417);
if (lean_is_scalar(x_1376)) {
 x_1419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1419 = x_1376;
}
lean_ctor_set(x_1419, 0, x_1418);
lean_ctor_set(x_1419, 1, x_1375);
return x_1419;
}
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1420 = l_Lean_Syntax_getArg(x_1186, x_1179);
lean_dec(x_1186);
lean_inc(x_5);
x_1421 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_1183, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
if (lean_obj_tag(x_1422) == 0)
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; uint8_t x_1435; 
lean_dec(x_1420);
x_1423 = lean_ctor_get(x_1421, 1);
lean_inc(x_1423);
lean_dec(x_1421);
lean_inc(x_5);
x_1424 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_1423);
x_1425 = lean_ctor_get(x_1424, 0);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_1424, 1);
lean_inc(x_1426);
lean_dec(x_1424);
x_1427 = lean_nat_add(x_3, x_1179);
lean_dec(x_3);
x_1428 = l_Lean_mkHole(x_19);
lean_inc(x_1425);
x_1429 = l_Lean_Elab_Term_mkExplicitBinder(x_1425, x_1428);
x_1430 = lean_array_push(x_4, x_1429);
lean_inc(x_5);
x_1431 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1427, x_1430, x_5, x_6, x_7, x_8, x_9, x_10, x_1426);
x_1432 = lean_ctor_get(x_1431, 0);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1432, 1);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1431, 1);
lean_inc(x_1434);
lean_dec(x_1431);
x_1435 = !lean_is_exclusive(x_1432);
if (x_1435 == 0)
{
lean_object* x_1436; uint8_t x_1437; 
x_1436 = lean_ctor_get(x_1432, 1);
lean_dec(x_1436);
x_1437 = !lean_is_exclusive(x_1433);
if (x_1437 == 0)
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; 
x_1438 = lean_ctor_get(x_1433, 0);
x_1439 = lean_ctor_get(x_1433, 1);
lean_dec(x_1439);
x_1440 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1434);
x_1441 = lean_ctor_get(x_1440, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1440, 1);
lean_inc(x_1442);
lean_dec(x_1440);
x_1443 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1442);
lean_dec(x_5);
x_1444 = lean_ctor_get(x_1443, 1);
lean_inc(x_1444);
lean_dec(x_1443);
x_1445 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1444);
x_1446 = !lean_is_exclusive(x_1445);
if (x_1446 == 0)
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; uint8_t x_1469; 
x_1447 = lean_ctor_get(x_1445, 0);
lean_dec(x_1447);
x_1448 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1441);
x_1449 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1449, 0, x_1441);
lean_ctor_set(x_1449, 1, x_1448);
x_1450 = l_Array_empty___closed__1;
x_1451 = lean_array_push(x_1450, x_1449);
x_1452 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1453 = lean_array_push(x_1452, x_1425);
x_1454 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1455, 0, x_1454);
lean_ctor_set(x_1455, 1, x_1453);
x_1456 = lean_array_push(x_1450, x_1455);
x_1457 = l_Lean_nullKind___closed__2;
x_1458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1458, 0, x_1457);
lean_ctor_set(x_1458, 1, x_1456);
x_1459 = lean_array_push(x_1451, x_1458);
x_1460 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1461 = lean_array_push(x_1459, x_1460);
x_1462 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1441);
x_1463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1463, 0, x_1441);
lean_ctor_set(x_1463, 1, x_1462);
x_1464 = lean_array_push(x_1461, x_1463);
x_1465 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1441);
x_1466 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1466, 0, x_1441);
lean_ctor_set(x_1466, 1, x_1465);
x_1467 = lean_array_push(x_1450, x_1466);
lean_inc(x_19);
x_1468 = lean_array_push(x_1450, x_19);
x_1469 = !lean_is_exclusive(x_19);
if (x_1469 == 0)
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; uint8_t x_1487; lean_object* x_1488; 
x_1470 = lean_ctor_get(x_19, 1);
lean_dec(x_1470);
x_1471 = lean_ctor_get(x_19, 0);
lean_dec(x_1471);
lean_ctor_set(x_19, 1, x_1468);
lean_ctor_set(x_19, 0, x_1457);
x_1472 = lean_array_push(x_1467, x_19);
x_1473 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1474 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1474, 0, x_1441);
lean_ctor_set(x_1474, 1, x_1473);
x_1475 = lean_array_push(x_1472, x_1474);
x_1476 = lean_array_push(x_1475, x_1438);
x_1477 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1478, 0, x_1477);
lean_ctor_set(x_1478, 1, x_1476);
x_1479 = lean_array_push(x_1450, x_1478);
x_1480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1480, 0, x_1457);
lean_ctor_set(x_1480, 1, x_1479);
x_1481 = lean_array_push(x_1450, x_1480);
x_1482 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1483, 0, x_1482);
lean_ctor_set(x_1483, 1, x_1481);
x_1484 = lean_array_push(x_1464, x_1483);
x_1485 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1486, 0, x_1485);
lean_ctor_set(x_1486, 1, x_1484);
x_1487 = 1;
x_1488 = lean_box(x_1487);
lean_ctor_set(x_1433, 1, x_1488);
lean_ctor_set(x_1433, 0, x_1486);
lean_ctor_set(x_1445, 0, x_1432);
return x_1445;
}
else
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; uint8_t x_1505; lean_object* x_1506; 
lean_dec(x_19);
x_1489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1489, 0, x_1457);
lean_ctor_set(x_1489, 1, x_1468);
x_1490 = lean_array_push(x_1467, x_1489);
x_1491 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1492 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1492, 0, x_1441);
lean_ctor_set(x_1492, 1, x_1491);
x_1493 = lean_array_push(x_1490, x_1492);
x_1494 = lean_array_push(x_1493, x_1438);
x_1495 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1496, 0, x_1495);
lean_ctor_set(x_1496, 1, x_1494);
x_1497 = lean_array_push(x_1450, x_1496);
x_1498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1498, 0, x_1457);
lean_ctor_set(x_1498, 1, x_1497);
x_1499 = lean_array_push(x_1450, x_1498);
x_1500 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1501, 0, x_1500);
lean_ctor_set(x_1501, 1, x_1499);
x_1502 = lean_array_push(x_1464, x_1501);
x_1503 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1504, 0, x_1503);
lean_ctor_set(x_1504, 1, x_1502);
x_1505 = 1;
x_1506 = lean_box(x_1505);
lean_ctor_set(x_1433, 1, x_1506);
lean_ctor_set(x_1433, 0, x_1504);
lean_ctor_set(x_1445, 0, x_1432);
return x_1445;
}
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; uint8_t x_1546; lean_object* x_1547; lean_object* x_1548; 
x_1507 = lean_ctor_get(x_1445, 1);
lean_inc(x_1507);
lean_dec(x_1445);
x_1508 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1441);
x_1509 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1509, 0, x_1441);
lean_ctor_set(x_1509, 1, x_1508);
x_1510 = l_Array_empty___closed__1;
x_1511 = lean_array_push(x_1510, x_1509);
x_1512 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1513 = lean_array_push(x_1512, x_1425);
x_1514 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1515, 0, x_1514);
lean_ctor_set(x_1515, 1, x_1513);
x_1516 = lean_array_push(x_1510, x_1515);
x_1517 = l_Lean_nullKind___closed__2;
x_1518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1518, 0, x_1517);
lean_ctor_set(x_1518, 1, x_1516);
x_1519 = lean_array_push(x_1511, x_1518);
x_1520 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1521 = lean_array_push(x_1519, x_1520);
x_1522 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1441);
x_1523 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1523, 0, x_1441);
lean_ctor_set(x_1523, 1, x_1522);
x_1524 = lean_array_push(x_1521, x_1523);
x_1525 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1441);
x_1526 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1526, 0, x_1441);
lean_ctor_set(x_1526, 1, x_1525);
x_1527 = lean_array_push(x_1510, x_1526);
lean_inc(x_19);
x_1528 = lean_array_push(x_1510, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1529 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1529 = lean_box(0);
}
if (lean_is_scalar(x_1529)) {
 x_1530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1530 = x_1529;
}
lean_ctor_set(x_1530, 0, x_1517);
lean_ctor_set(x_1530, 1, x_1528);
x_1531 = lean_array_push(x_1527, x_1530);
x_1532 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1533 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1533, 0, x_1441);
lean_ctor_set(x_1533, 1, x_1532);
x_1534 = lean_array_push(x_1531, x_1533);
x_1535 = lean_array_push(x_1534, x_1438);
x_1536 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1537, 0, x_1536);
lean_ctor_set(x_1537, 1, x_1535);
x_1538 = lean_array_push(x_1510, x_1537);
x_1539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1539, 0, x_1517);
lean_ctor_set(x_1539, 1, x_1538);
x_1540 = lean_array_push(x_1510, x_1539);
x_1541 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1542, 0, x_1541);
lean_ctor_set(x_1542, 1, x_1540);
x_1543 = lean_array_push(x_1524, x_1542);
x_1544 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1545, 0, x_1544);
lean_ctor_set(x_1545, 1, x_1543);
x_1546 = 1;
x_1547 = lean_box(x_1546);
lean_ctor_set(x_1433, 1, x_1547);
lean_ctor_set(x_1433, 0, x_1545);
x_1548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1548, 0, x_1432);
lean_ctor_set(x_1548, 1, x_1507);
return x_1548;
}
}
else
{
lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; uint8_t x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1549 = lean_ctor_get(x_1433, 0);
lean_inc(x_1549);
lean_dec(x_1433);
x_1550 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1434);
x_1551 = lean_ctor_get(x_1550, 0);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1550, 1);
lean_inc(x_1552);
lean_dec(x_1550);
x_1553 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1552);
lean_dec(x_5);
x_1554 = lean_ctor_get(x_1553, 1);
lean_inc(x_1554);
lean_dec(x_1553);
x_1555 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1554);
x_1556 = lean_ctor_get(x_1555, 1);
lean_inc(x_1556);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1557 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1557 = lean_box(0);
}
x_1558 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1551);
x_1559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1559, 0, x_1551);
lean_ctor_set(x_1559, 1, x_1558);
x_1560 = l_Array_empty___closed__1;
x_1561 = lean_array_push(x_1560, x_1559);
x_1562 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1563 = lean_array_push(x_1562, x_1425);
x_1564 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1565, 0, x_1564);
lean_ctor_set(x_1565, 1, x_1563);
x_1566 = lean_array_push(x_1560, x_1565);
x_1567 = l_Lean_nullKind___closed__2;
x_1568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1568, 0, x_1567);
lean_ctor_set(x_1568, 1, x_1566);
x_1569 = lean_array_push(x_1561, x_1568);
x_1570 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1571 = lean_array_push(x_1569, x_1570);
x_1572 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1551);
x_1573 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1573, 0, x_1551);
lean_ctor_set(x_1573, 1, x_1572);
x_1574 = lean_array_push(x_1571, x_1573);
x_1575 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1551);
x_1576 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1576, 0, x_1551);
lean_ctor_set(x_1576, 1, x_1575);
x_1577 = lean_array_push(x_1560, x_1576);
lean_inc(x_19);
x_1578 = lean_array_push(x_1560, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1579 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1579 = lean_box(0);
}
if (lean_is_scalar(x_1579)) {
 x_1580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1580 = x_1579;
}
lean_ctor_set(x_1580, 0, x_1567);
lean_ctor_set(x_1580, 1, x_1578);
x_1581 = lean_array_push(x_1577, x_1580);
x_1582 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1583 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1583, 0, x_1551);
lean_ctor_set(x_1583, 1, x_1582);
x_1584 = lean_array_push(x_1581, x_1583);
x_1585 = lean_array_push(x_1584, x_1549);
x_1586 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1587, 0, x_1586);
lean_ctor_set(x_1587, 1, x_1585);
x_1588 = lean_array_push(x_1560, x_1587);
x_1589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1589, 0, x_1567);
lean_ctor_set(x_1589, 1, x_1588);
x_1590 = lean_array_push(x_1560, x_1589);
x_1591 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1592, 0, x_1591);
lean_ctor_set(x_1592, 1, x_1590);
x_1593 = lean_array_push(x_1574, x_1592);
x_1594 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1595, 0, x_1594);
lean_ctor_set(x_1595, 1, x_1593);
x_1596 = 1;
x_1597 = lean_box(x_1596);
x_1598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1598, 0, x_1595);
lean_ctor_set(x_1598, 1, x_1597);
lean_ctor_set(x_1432, 1, x_1598);
if (lean_is_scalar(x_1557)) {
 x_1599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1599 = x_1557;
}
lean_ctor_set(x_1599, 0, x_1432);
lean_ctor_set(x_1599, 1, x_1556);
return x_1599;
}
}
else
{
lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; uint8_t x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; 
x_1600 = lean_ctor_get(x_1432, 0);
lean_inc(x_1600);
lean_dec(x_1432);
x_1601 = lean_ctor_get(x_1433, 0);
lean_inc(x_1601);
if (lean_is_exclusive(x_1433)) {
 lean_ctor_release(x_1433, 0);
 lean_ctor_release(x_1433, 1);
 x_1602 = x_1433;
} else {
 lean_dec_ref(x_1433);
 x_1602 = lean_box(0);
}
x_1603 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1434);
x_1604 = lean_ctor_get(x_1603, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1603, 1);
lean_inc(x_1605);
lean_dec(x_1603);
x_1606 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1605);
lean_dec(x_5);
x_1607 = lean_ctor_get(x_1606, 1);
lean_inc(x_1607);
lean_dec(x_1606);
x_1608 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1607);
x_1609 = lean_ctor_get(x_1608, 1);
lean_inc(x_1609);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1610 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1610 = lean_box(0);
}
x_1611 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1604);
x_1612 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1612, 0, x_1604);
lean_ctor_set(x_1612, 1, x_1611);
x_1613 = l_Array_empty___closed__1;
x_1614 = lean_array_push(x_1613, x_1612);
x_1615 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1616 = lean_array_push(x_1615, x_1425);
x_1617 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1618, 0, x_1617);
lean_ctor_set(x_1618, 1, x_1616);
x_1619 = lean_array_push(x_1613, x_1618);
x_1620 = l_Lean_nullKind___closed__2;
x_1621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1621, 0, x_1620);
lean_ctor_set(x_1621, 1, x_1619);
x_1622 = lean_array_push(x_1614, x_1621);
x_1623 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1624 = lean_array_push(x_1622, x_1623);
x_1625 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1604);
x_1626 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1626, 0, x_1604);
lean_ctor_set(x_1626, 1, x_1625);
x_1627 = lean_array_push(x_1624, x_1626);
x_1628 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1604);
x_1629 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1629, 0, x_1604);
lean_ctor_set(x_1629, 1, x_1628);
x_1630 = lean_array_push(x_1613, x_1629);
lean_inc(x_19);
x_1631 = lean_array_push(x_1613, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1632 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1632 = lean_box(0);
}
if (lean_is_scalar(x_1632)) {
 x_1633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1633 = x_1632;
}
lean_ctor_set(x_1633, 0, x_1620);
lean_ctor_set(x_1633, 1, x_1631);
x_1634 = lean_array_push(x_1630, x_1633);
x_1635 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1636 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1636, 0, x_1604);
lean_ctor_set(x_1636, 1, x_1635);
x_1637 = lean_array_push(x_1634, x_1636);
x_1638 = lean_array_push(x_1637, x_1601);
x_1639 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1640, 0, x_1639);
lean_ctor_set(x_1640, 1, x_1638);
x_1641 = lean_array_push(x_1613, x_1640);
x_1642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1642, 0, x_1620);
lean_ctor_set(x_1642, 1, x_1641);
x_1643 = lean_array_push(x_1613, x_1642);
x_1644 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1645, 0, x_1644);
lean_ctor_set(x_1645, 1, x_1643);
x_1646 = lean_array_push(x_1627, x_1645);
x_1647 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1648, 0, x_1647);
lean_ctor_set(x_1648, 1, x_1646);
x_1649 = 1;
x_1650 = lean_box(x_1649);
if (lean_is_scalar(x_1602)) {
 x_1651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1651 = x_1602;
}
lean_ctor_set(x_1651, 0, x_1648);
lean_ctor_set(x_1651, 1, x_1650);
x_1652 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1652, 0, x_1600);
lean_ctor_set(x_1652, 1, x_1651);
if (lean_is_scalar(x_1610)) {
 x_1653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1653 = x_1610;
}
lean_ctor_set(x_1653, 0, x_1652);
lean_ctor_set(x_1653, 1, x_1609);
return x_1653;
}
}
else
{
lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; size_t x_1658; size_t x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; 
lean_dec(x_19);
x_1654 = lean_ctor_get(x_1421, 1);
lean_inc(x_1654);
lean_dec(x_1421);
x_1655 = lean_ctor_get(x_1422, 0);
lean_inc(x_1655);
lean_dec(x_1422);
x_1656 = lean_nat_add(x_3, x_1179);
lean_dec(x_3);
x_1657 = lean_array_get_size(x_1655);
x_1658 = lean_usize_of_nat(x_1657);
lean_dec(x_1657);
x_1659 = 0;
x_1660 = x_1655;
x_1661 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_1420, x_1658, x_1659, x_1660);
x_1662 = x_1661;
x_1663 = l_Array_append___rarg(x_4, x_1662);
lean_dec(x_1662);
x_3 = x_1656;
x_4 = x_1663;
x_11 = x_1654;
goto _start;
}
}
}
else
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; uint8_t x_1676; 
lean_dec(x_1184);
lean_dec(x_1183);
lean_inc(x_5);
x_1665 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_1666 = lean_ctor_get(x_1665, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1665, 1);
lean_inc(x_1667);
lean_dec(x_1665);
x_1668 = lean_nat_add(x_3, x_1179);
lean_dec(x_3);
x_1669 = l_Lean_mkHole(x_19);
lean_inc(x_1666);
x_1670 = l_Lean_Elab_Term_mkExplicitBinder(x_1666, x_1669);
x_1671 = lean_array_push(x_4, x_1670);
lean_inc(x_5);
x_1672 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1668, x_1671, x_5, x_6, x_7, x_8, x_9, x_10, x_1667);
x_1673 = lean_ctor_get(x_1672, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1673, 1);
lean_inc(x_1674);
x_1675 = lean_ctor_get(x_1672, 1);
lean_inc(x_1675);
lean_dec(x_1672);
x_1676 = !lean_is_exclusive(x_1673);
if (x_1676 == 0)
{
lean_object* x_1677; uint8_t x_1678; 
x_1677 = lean_ctor_get(x_1673, 1);
lean_dec(x_1677);
x_1678 = !lean_is_exclusive(x_1674);
if (x_1678 == 0)
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; uint8_t x_1687; 
x_1679 = lean_ctor_get(x_1674, 0);
x_1680 = lean_ctor_get(x_1674, 1);
lean_dec(x_1680);
x_1681 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1675);
x_1682 = lean_ctor_get(x_1681, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1681, 1);
lean_inc(x_1683);
lean_dec(x_1681);
x_1684 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1683);
lean_dec(x_5);
x_1685 = lean_ctor_get(x_1684, 1);
lean_inc(x_1685);
lean_dec(x_1684);
x_1686 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1685);
x_1687 = !lean_is_exclusive(x_1686);
if (x_1687 == 0)
{
lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; uint8_t x_1710; 
x_1688 = lean_ctor_get(x_1686, 0);
lean_dec(x_1688);
x_1689 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1682);
x_1690 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1690, 0, x_1682);
lean_ctor_set(x_1690, 1, x_1689);
x_1691 = l_Array_empty___closed__1;
x_1692 = lean_array_push(x_1691, x_1690);
x_1693 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1694 = lean_array_push(x_1693, x_1666);
x_1695 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1696, 0, x_1695);
lean_ctor_set(x_1696, 1, x_1694);
x_1697 = lean_array_push(x_1691, x_1696);
x_1698 = l_Lean_nullKind___closed__2;
x_1699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1699, 0, x_1698);
lean_ctor_set(x_1699, 1, x_1697);
x_1700 = lean_array_push(x_1692, x_1699);
x_1701 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1702 = lean_array_push(x_1700, x_1701);
x_1703 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1682);
x_1704 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1704, 0, x_1682);
lean_ctor_set(x_1704, 1, x_1703);
x_1705 = lean_array_push(x_1702, x_1704);
x_1706 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1682);
x_1707 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1707, 0, x_1682);
lean_ctor_set(x_1707, 1, x_1706);
x_1708 = lean_array_push(x_1691, x_1707);
lean_inc(x_19);
x_1709 = lean_array_push(x_1691, x_19);
x_1710 = !lean_is_exclusive(x_19);
if (x_1710 == 0)
{
lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; uint8_t x_1728; lean_object* x_1729; 
x_1711 = lean_ctor_get(x_19, 1);
lean_dec(x_1711);
x_1712 = lean_ctor_get(x_19, 0);
lean_dec(x_1712);
lean_ctor_set(x_19, 1, x_1709);
lean_ctor_set(x_19, 0, x_1698);
x_1713 = lean_array_push(x_1708, x_19);
x_1714 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1715 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1715, 0, x_1682);
lean_ctor_set(x_1715, 1, x_1714);
x_1716 = lean_array_push(x_1713, x_1715);
x_1717 = lean_array_push(x_1716, x_1679);
x_1718 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1719, 0, x_1718);
lean_ctor_set(x_1719, 1, x_1717);
x_1720 = lean_array_push(x_1691, x_1719);
x_1721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1721, 0, x_1698);
lean_ctor_set(x_1721, 1, x_1720);
x_1722 = lean_array_push(x_1691, x_1721);
x_1723 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1724, 0, x_1723);
lean_ctor_set(x_1724, 1, x_1722);
x_1725 = lean_array_push(x_1705, x_1724);
x_1726 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1727, 0, x_1726);
lean_ctor_set(x_1727, 1, x_1725);
x_1728 = 1;
x_1729 = lean_box(x_1728);
lean_ctor_set(x_1674, 1, x_1729);
lean_ctor_set(x_1674, 0, x_1727);
lean_ctor_set(x_1686, 0, x_1673);
return x_1686;
}
else
{
lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; uint8_t x_1746; lean_object* x_1747; 
lean_dec(x_19);
x_1730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1730, 0, x_1698);
lean_ctor_set(x_1730, 1, x_1709);
x_1731 = lean_array_push(x_1708, x_1730);
x_1732 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1733 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1733, 0, x_1682);
lean_ctor_set(x_1733, 1, x_1732);
x_1734 = lean_array_push(x_1731, x_1733);
x_1735 = lean_array_push(x_1734, x_1679);
x_1736 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1737, 0, x_1736);
lean_ctor_set(x_1737, 1, x_1735);
x_1738 = lean_array_push(x_1691, x_1737);
x_1739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1739, 0, x_1698);
lean_ctor_set(x_1739, 1, x_1738);
x_1740 = lean_array_push(x_1691, x_1739);
x_1741 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1742, 0, x_1741);
lean_ctor_set(x_1742, 1, x_1740);
x_1743 = lean_array_push(x_1705, x_1742);
x_1744 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1745, 0, x_1744);
lean_ctor_set(x_1745, 1, x_1743);
x_1746 = 1;
x_1747 = lean_box(x_1746);
lean_ctor_set(x_1674, 1, x_1747);
lean_ctor_set(x_1674, 0, x_1745);
lean_ctor_set(x_1686, 0, x_1673);
return x_1686;
}
}
else
{
lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; uint8_t x_1787; lean_object* x_1788; lean_object* x_1789; 
x_1748 = lean_ctor_get(x_1686, 1);
lean_inc(x_1748);
lean_dec(x_1686);
x_1749 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1682);
x_1750 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1750, 0, x_1682);
lean_ctor_set(x_1750, 1, x_1749);
x_1751 = l_Array_empty___closed__1;
x_1752 = lean_array_push(x_1751, x_1750);
x_1753 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1754 = lean_array_push(x_1753, x_1666);
x_1755 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1756, 0, x_1755);
lean_ctor_set(x_1756, 1, x_1754);
x_1757 = lean_array_push(x_1751, x_1756);
x_1758 = l_Lean_nullKind___closed__2;
x_1759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1759, 0, x_1758);
lean_ctor_set(x_1759, 1, x_1757);
x_1760 = lean_array_push(x_1752, x_1759);
x_1761 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1762 = lean_array_push(x_1760, x_1761);
x_1763 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1682);
x_1764 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1764, 0, x_1682);
lean_ctor_set(x_1764, 1, x_1763);
x_1765 = lean_array_push(x_1762, x_1764);
x_1766 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1682);
x_1767 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1767, 0, x_1682);
lean_ctor_set(x_1767, 1, x_1766);
x_1768 = lean_array_push(x_1751, x_1767);
lean_inc(x_19);
x_1769 = lean_array_push(x_1751, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1770 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1770 = lean_box(0);
}
if (lean_is_scalar(x_1770)) {
 x_1771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1771 = x_1770;
}
lean_ctor_set(x_1771, 0, x_1758);
lean_ctor_set(x_1771, 1, x_1769);
x_1772 = lean_array_push(x_1768, x_1771);
x_1773 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1774 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1774, 0, x_1682);
lean_ctor_set(x_1774, 1, x_1773);
x_1775 = lean_array_push(x_1772, x_1774);
x_1776 = lean_array_push(x_1775, x_1679);
x_1777 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1778, 0, x_1777);
lean_ctor_set(x_1778, 1, x_1776);
x_1779 = lean_array_push(x_1751, x_1778);
x_1780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1780, 0, x_1758);
lean_ctor_set(x_1780, 1, x_1779);
x_1781 = lean_array_push(x_1751, x_1780);
x_1782 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1783, 0, x_1782);
lean_ctor_set(x_1783, 1, x_1781);
x_1784 = lean_array_push(x_1765, x_1783);
x_1785 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1786, 0, x_1785);
lean_ctor_set(x_1786, 1, x_1784);
x_1787 = 1;
x_1788 = lean_box(x_1787);
lean_ctor_set(x_1674, 1, x_1788);
lean_ctor_set(x_1674, 0, x_1786);
x_1789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1789, 0, x_1673);
lean_ctor_set(x_1789, 1, x_1748);
return x_1789;
}
}
else
{
lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; uint8_t x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; 
x_1790 = lean_ctor_get(x_1674, 0);
lean_inc(x_1790);
lean_dec(x_1674);
x_1791 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1675);
x_1792 = lean_ctor_get(x_1791, 0);
lean_inc(x_1792);
x_1793 = lean_ctor_get(x_1791, 1);
lean_inc(x_1793);
lean_dec(x_1791);
x_1794 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1793);
lean_dec(x_5);
x_1795 = lean_ctor_get(x_1794, 1);
lean_inc(x_1795);
lean_dec(x_1794);
x_1796 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1795);
x_1797 = lean_ctor_get(x_1796, 1);
lean_inc(x_1797);
if (lean_is_exclusive(x_1796)) {
 lean_ctor_release(x_1796, 0);
 lean_ctor_release(x_1796, 1);
 x_1798 = x_1796;
} else {
 lean_dec_ref(x_1796);
 x_1798 = lean_box(0);
}
x_1799 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1792);
x_1800 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1800, 0, x_1792);
lean_ctor_set(x_1800, 1, x_1799);
x_1801 = l_Array_empty___closed__1;
x_1802 = lean_array_push(x_1801, x_1800);
x_1803 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1804 = lean_array_push(x_1803, x_1666);
x_1805 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1806, 0, x_1805);
lean_ctor_set(x_1806, 1, x_1804);
x_1807 = lean_array_push(x_1801, x_1806);
x_1808 = l_Lean_nullKind___closed__2;
x_1809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1809, 0, x_1808);
lean_ctor_set(x_1809, 1, x_1807);
x_1810 = lean_array_push(x_1802, x_1809);
x_1811 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1812 = lean_array_push(x_1810, x_1811);
x_1813 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1792);
x_1814 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1814, 0, x_1792);
lean_ctor_set(x_1814, 1, x_1813);
x_1815 = lean_array_push(x_1812, x_1814);
x_1816 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1792);
x_1817 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1817, 0, x_1792);
lean_ctor_set(x_1817, 1, x_1816);
x_1818 = lean_array_push(x_1801, x_1817);
lean_inc(x_19);
x_1819 = lean_array_push(x_1801, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1820 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1820 = lean_box(0);
}
if (lean_is_scalar(x_1820)) {
 x_1821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1821 = x_1820;
}
lean_ctor_set(x_1821, 0, x_1808);
lean_ctor_set(x_1821, 1, x_1819);
x_1822 = lean_array_push(x_1818, x_1821);
x_1823 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1824 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1824, 0, x_1792);
lean_ctor_set(x_1824, 1, x_1823);
x_1825 = lean_array_push(x_1822, x_1824);
x_1826 = lean_array_push(x_1825, x_1790);
x_1827 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1828, 0, x_1827);
lean_ctor_set(x_1828, 1, x_1826);
x_1829 = lean_array_push(x_1801, x_1828);
x_1830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1830, 0, x_1808);
lean_ctor_set(x_1830, 1, x_1829);
x_1831 = lean_array_push(x_1801, x_1830);
x_1832 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1833, 0, x_1832);
lean_ctor_set(x_1833, 1, x_1831);
x_1834 = lean_array_push(x_1815, x_1833);
x_1835 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1836, 0, x_1835);
lean_ctor_set(x_1836, 1, x_1834);
x_1837 = 1;
x_1838 = lean_box(x_1837);
x_1839 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1839, 0, x_1836);
lean_ctor_set(x_1839, 1, x_1838);
lean_ctor_set(x_1673, 1, x_1839);
if (lean_is_scalar(x_1798)) {
 x_1840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1840 = x_1798;
}
lean_ctor_set(x_1840, 0, x_1673);
lean_ctor_set(x_1840, 1, x_1797);
return x_1840;
}
}
else
{
lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; uint8_t x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
x_1841 = lean_ctor_get(x_1673, 0);
lean_inc(x_1841);
lean_dec(x_1673);
x_1842 = lean_ctor_get(x_1674, 0);
lean_inc(x_1842);
if (lean_is_exclusive(x_1674)) {
 lean_ctor_release(x_1674, 0);
 lean_ctor_release(x_1674, 1);
 x_1843 = x_1674;
} else {
 lean_dec_ref(x_1674);
 x_1843 = lean_box(0);
}
x_1844 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1675);
x_1845 = lean_ctor_get(x_1844, 0);
lean_inc(x_1845);
x_1846 = lean_ctor_get(x_1844, 1);
lean_inc(x_1846);
lean_dec(x_1844);
x_1847 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1846);
lean_dec(x_5);
x_1848 = lean_ctor_get(x_1847, 1);
lean_inc(x_1848);
lean_dec(x_1847);
x_1849 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1848);
x_1850 = lean_ctor_get(x_1849, 1);
lean_inc(x_1850);
if (lean_is_exclusive(x_1849)) {
 lean_ctor_release(x_1849, 0);
 lean_ctor_release(x_1849, 1);
 x_1851 = x_1849;
} else {
 lean_dec_ref(x_1849);
 x_1851 = lean_box(0);
}
x_1852 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1845);
x_1853 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1853, 0, x_1845);
lean_ctor_set(x_1853, 1, x_1852);
x_1854 = l_Array_empty___closed__1;
x_1855 = lean_array_push(x_1854, x_1853);
x_1856 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1857 = lean_array_push(x_1856, x_1666);
x_1858 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1859, 0, x_1858);
lean_ctor_set(x_1859, 1, x_1857);
x_1860 = lean_array_push(x_1854, x_1859);
x_1861 = l_Lean_nullKind___closed__2;
x_1862 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1862, 0, x_1861);
lean_ctor_set(x_1862, 1, x_1860);
x_1863 = lean_array_push(x_1855, x_1862);
x_1864 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1865 = lean_array_push(x_1863, x_1864);
x_1866 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1845);
x_1867 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1867, 0, x_1845);
lean_ctor_set(x_1867, 1, x_1866);
x_1868 = lean_array_push(x_1865, x_1867);
x_1869 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1845);
x_1870 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1870, 0, x_1845);
lean_ctor_set(x_1870, 1, x_1869);
x_1871 = lean_array_push(x_1854, x_1870);
lean_inc(x_19);
x_1872 = lean_array_push(x_1854, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_1873 = x_19;
} else {
 lean_dec_ref(x_19);
 x_1873 = lean_box(0);
}
if (lean_is_scalar(x_1873)) {
 x_1874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1874 = x_1873;
}
lean_ctor_set(x_1874, 0, x_1861);
lean_ctor_set(x_1874, 1, x_1872);
x_1875 = lean_array_push(x_1871, x_1874);
x_1876 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1877 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1877, 0, x_1845);
lean_ctor_set(x_1877, 1, x_1876);
x_1878 = lean_array_push(x_1875, x_1877);
x_1879 = lean_array_push(x_1878, x_1842);
x_1880 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1881, 0, x_1880);
lean_ctor_set(x_1881, 1, x_1879);
x_1882 = lean_array_push(x_1854, x_1881);
x_1883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1883, 0, x_1861);
lean_ctor_set(x_1883, 1, x_1882);
x_1884 = lean_array_push(x_1854, x_1883);
x_1885 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1886, 0, x_1885);
lean_ctor_set(x_1886, 1, x_1884);
x_1887 = lean_array_push(x_1868, x_1886);
x_1888 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1889, 0, x_1888);
lean_ctor_set(x_1889, 1, x_1887);
x_1890 = 1;
x_1891 = lean_box(x_1890);
if (lean_is_scalar(x_1843)) {
 x_1892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1892 = x_1843;
}
lean_ctor_set(x_1892, 0, x_1889);
lean_ctor_set(x_1892, 1, x_1891);
x_1893 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1893, 0, x_1841);
lean_ctor_set(x_1893, 1, x_1892);
if (lean_is_scalar(x_1851)) {
 x_1894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1894 = x_1851;
}
lean_ctor_set(x_1894, 0, x_1893);
lean_ctor_set(x_1894, 1, x_1850);
return x_1894;
}
}
}
else
{
lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; uint8_t x_1906; 
lean_dec(x_1180);
lean_inc(x_5);
x_1895 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_1896 = lean_ctor_get(x_1895, 0);
lean_inc(x_1896);
x_1897 = lean_ctor_get(x_1895, 1);
lean_inc(x_1897);
lean_dec(x_1895);
x_1898 = lean_nat_add(x_3, x_1179);
lean_dec(x_3);
x_1899 = l_Lean_mkHole(x_19);
lean_inc(x_1896);
x_1900 = l_Lean_Elab_Term_mkExplicitBinder(x_1896, x_1899);
x_1901 = lean_array_push(x_4, x_1900);
lean_inc(x_5);
x_1902 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1898, x_1901, x_5, x_6, x_7, x_8, x_9, x_10, x_1897);
x_1903 = lean_ctor_get(x_1902, 0);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1903, 1);
lean_inc(x_1904);
x_1905 = lean_ctor_get(x_1902, 1);
lean_inc(x_1905);
lean_dec(x_1902);
x_1906 = !lean_is_exclusive(x_1903);
if (x_1906 == 0)
{
lean_object* x_1907; uint8_t x_1908; 
x_1907 = lean_ctor_get(x_1903, 1);
lean_dec(x_1907);
x_1908 = !lean_is_exclusive(x_1904);
if (x_1908 == 0)
{
lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; uint8_t x_1917; 
x_1909 = lean_ctor_get(x_1904, 0);
x_1910 = lean_ctor_get(x_1904, 1);
lean_dec(x_1910);
x_1911 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1905);
x_1912 = lean_ctor_get(x_1911, 0);
lean_inc(x_1912);
x_1913 = lean_ctor_get(x_1911, 1);
lean_inc(x_1913);
lean_dec(x_1911);
x_1914 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_1913);
lean_dec(x_5);
x_1915 = lean_ctor_get(x_1914, 1);
lean_inc(x_1915);
lean_dec(x_1914);
x_1916 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_1915);
x_1917 = !lean_is_exclusive(x_1916);
if (x_1917 == 0)
{
lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; uint8_t x_1940; 
x_1918 = lean_ctor_get(x_1916, 0);
lean_dec(x_1918);
x_1919 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1912);
x_1920 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1920, 0, x_1912);
lean_ctor_set(x_1920, 1, x_1919);
x_1921 = l_Array_empty___closed__1;
x_1922 = lean_array_push(x_1921, x_1920);
x_1923 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1924 = lean_array_push(x_1923, x_1896);
x_1925 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1926 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1926, 0, x_1925);
lean_ctor_set(x_1926, 1, x_1924);
x_1927 = lean_array_push(x_1921, x_1926);
x_1928 = l_Lean_nullKind___closed__2;
x_1929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1929, 0, x_1928);
lean_ctor_set(x_1929, 1, x_1927);
x_1930 = lean_array_push(x_1922, x_1929);
x_1931 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1932 = lean_array_push(x_1930, x_1931);
x_1933 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1912);
x_1934 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1934, 0, x_1912);
lean_ctor_set(x_1934, 1, x_1933);
x_1935 = lean_array_push(x_1932, x_1934);
x_1936 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1912);
x_1937 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1937, 0, x_1912);
lean_ctor_set(x_1937, 1, x_1936);
x_1938 = lean_array_push(x_1921, x_1937);
lean_inc(x_19);
x_1939 = lean_array_push(x_1921, x_19);
x_1940 = !lean_is_exclusive(x_19);
if (x_1940 == 0)
{
lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; uint8_t x_1958; lean_object* x_1959; 
x_1941 = lean_ctor_get(x_19, 1);
lean_dec(x_1941);
x_1942 = lean_ctor_get(x_19, 0);
lean_dec(x_1942);
lean_ctor_set(x_19, 1, x_1939);
lean_ctor_set(x_19, 0, x_1928);
x_1943 = lean_array_push(x_1938, x_19);
x_1944 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1945 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1945, 0, x_1912);
lean_ctor_set(x_1945, 1, x_1944);
x_1946 = lean_array_push(x_1943, x_1945);
x_1947 = lean_array_push(x_1946, x_1909);
x_1948 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1949 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1949, 0, x_1948);
lean_ctor_set(x_1949, 1, x_1947);
x_1950 = lean_array_push(x_1921, x_1949);
x_1951 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1951, 0, x_1928);
lean_ctor_set(x_1951, 1, x_1950);
x_1952 = lean_array_push(x_1921, x_1951);
x_1953 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1954 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1954, 0, x_1953);
lean_ctor_set(x_1954, 1, x_1952);
x_1955 = lean_array_push(x_1935, x_1954);
x_1956 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1957 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1957, 0, x_1956);
lean_ctor_set(x_1957, 1, x_1955);
x_1958 = 1;
x_1959 = lean_box(x_1958);
lean_ctor_set(x_1904, 1, x_1959);
lean_ctor_set(x_1904, 0, x_1957);
lean_ctor_set(x_1916, 0, x_1903);
return x_1916;
}
else
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; uint8_t x_1976; lean_object* x_1977; 
lean_dec(x_19);
x_1960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1960, 0, x_1928);
lean_ctor_set(x_1960, 1, x_1939);
x_1961 = lean_array_push(x_1938, x_1960);
x_1962 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_1963 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1963, 0, x_1912);
lean_ctor_set(x_1963, 1, x_1962);
x_1964 = lean_array_push(x_1961, x_1963);
x_1965 = lean_array_push(x_1964, x_1909);
x_1966 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_1967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1967, 0, x_1966);
lean_ctor_set(x_1967, 1, x_1965);
x_1968 = lean_array_push(x_1921, x_1967);
x_1969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1969, 0, x_1928);
lean_ctor_set(x_1969, 1, x_1968);
x_1970 = lean_array_push(x_1921, x_1969);
x_1971 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_1972 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1972, 0, x_1971);
lean_ctor_set(x_1972, 1, x_1970);
x_1973 = lean_array_push(x_1935, x_1972);
x_1974 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_1975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1975, 0, x_1974);
lean_ctor_set(x_1975, 1, x_1973);
x_1976 = 1;
x_1977 = lean_box(x_1976);
lean_ctor_set(x_1904, 1, x_1977);
lean_ctor_set(x_1904, 0, x_1975);
lean_ctor_set(x_1916, 0, x_1903);
return x_1916;
}
}
else
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; uint8_t x_2017; lean_object* x_2018; lean_object* x_2019; 
x_1978 = lean_ctor_get(x_1916, 1);
lean_inc(x_1978);
lean_dec(x_1916);
x_1979 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_1912);
x_1980 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1980, 0, x_1912);
lean_ctor_set(x_1980, 1, x_1979);
x_1981 = l_Array_empty___closed__1;
x_1982 = lean_array_push(x_1981, x_1980);
x_1983 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_1984 = lean_array_push(x_1983, x_1896);
x_1985 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_1986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1986, 0, x_1985);
lean_ctor_set(x_1986, 1, x_1984);
x_1987 = lean_array_push(x_1981, x_1986);
x_1988 = l_Lean_nullKind___closed__2;
x_1989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1989, 0, x_1988);
lean_ctor_set(x_1989, 1, x_1987);
x_1990 = lean_array_push(x_1982, x_1989);
x_1991 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_1992 = lean_array_push(x_1990, x_1991);
x_1993 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_1912);
x_1994 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1994, 0, x_1912);
lean_ctor_set(x_1994, 1, x_1993);
x_1995 = lean_array_push(x_1992, x_1994);
x_1996 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_1912);
x_1997 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1997, 0, x_1912);
lean_ctor_set(x_1997, 1, x_1996);
x_1998 = lean_array_push(x_1981, x_1997);
lean_inc(x_19);
x_1999 = lean_array_push(x_1981, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2000 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2000 = lean_box(0);
}
if (lean_is_scalar(x_2000)) {
 x_2001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2001 = x_2000;
}
lean_ctor_set(x_2001, 0, x_1988);
lean_ctor_set(x_2001, 1, x_1999);
x_2002 = lean_array_push(x_1998, x_2001);
x_2003 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2004 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2004, 0, x_1912);
lean_ctor_set(x_2004, 1, x_2003);
x_2005 = lean_array_push(x_2002, x_2004);
x_2006 = lean_array_push(x_2005, x_1909);
x_2007 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2008, 0, x_2007);
lean_ctor_set(x_2008, 1, x_2006);
x_2009 = lean_array_push(x_1981, x_2008);
x_2010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2010, 0, x_1988);
lean_ctor_set(x_2010, 1, x_2009);
x_2011 = lean_array_push(x_1981, x_2010);
x_2012 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2013, 0, x_2012);
lean_ctor_set(x_2013, 1, x_2011);
x_2014 = lean_array_push(x_1995, x_2013);
x_2015 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2016, 0, x_2015);
lean_ctor_set(x_2016, 1, x_2014);
x_2017 = 1;
x_2018 = lean_box(x_2017);
lean_ctor_set(x_1904, 1, x_2018);
lean_ctor_set(x_1904, 0, x_2016);
x_2019 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2019, 0, x_1903);
lean_ctor_set(x_2019, 1, x_1978);
return x_2019;
}
}
else
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; uint8_t x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; 
x_2020 = lean_ctor_get(x_1904, 0);
lean_inc(x_2020);
lean_dec(x_1904);
x_2021 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1905);
x_2022 = lean_ctor_get(x_2021, 0);
lean_inc(x_2022);
x_2023 = lean_ctor_get(x_2021, 1);
lean_inc(x_2023);
lean_dec(x_2021);
x_2024 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2023);
lean_dec(x_5);
x_2025 = lean_ctor_get(x_2024, 1);
lean_inc(x_2025);
lean_dec(x_2024);
x_2026 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2025);
x_2027 = lean_ctor_get(x_2026, 1);
lean_inc(x_2027);
if (lean_is_exclusive(x_2026)) {
 lean_ctor_release(x_2026, 0);
 lean_ctor_release(x_2026, 1);
 x_2028 = x_2026;
} else {
 lean_dec_ref(x_2026);
 x_2028 = lean_box(0);
}
x_2029 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2022);
x_2030 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2030, 0, x_2022);
lean_ctor_set(x_2030, 1, x_2029);
x_2031 = l_Array_empty___closed__1;
x_2032 = lean_array_push(x_2031, x_2030);
x_2033 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2034 = lean_array_push(x_2033, x_1896);
x_2035 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2036 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2036, 0, x_2035);
lean_ctor_set(x_2036, 1, x_2034);
x_2037 = lean_array_push(x_2031, x_2036);
x_2038 = l_Lean_nullKind___closed__2;
x_2039 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2039, 0, x_2038);
lean_ctor_set(x_2039, 1, x_2037);
x_2040 = lean_array_push(x_2032, x_2039);
x_2041 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2042 = lean_array_push(x_2040, x_2041);
x_2043 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2022);
x_2044 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2044, 0, x_2022);
lean_ctor_set(x_2044, 1, x_2043);
x_2045 = lean_array_push(x_2042, x_2044);
x_2046 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2022);
x_2047 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2047, 0, x_2022);
lean_ctor_set(x_2047, 1, x_2046);
x_2048 = lean_array_push(x_2031, x_2047);
lean_inc(x_19);
x_2049 = lean_array_push(x_2031, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2050 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2050 = lean_box(0);
}
if (lean_is_scalar(x_2050)) {
 x_2051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2051 = x_2050;
}
lean_ctor_set(x_2051, 0, x_2038);
lean_ctor_set(x_2051, 1, x_2049);
x_2052 = lean_array_push(x_2048, x_2051);
x_2053 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2054 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2054, 0, x_2022);
lean_ctor_set(x_2054, 1, x_2053);
x_2055 = lean_array_push(x_2052, x_2054);
x_2056 = lean_array_push(x_2055, x_2020);
x_2057 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2058 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2058, 0, x_2057);
lean_ctor_set(x_2058, 1, x_2056);
x_2059 = lean_array_push(x_2031, x_2058);
x_2060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2060, 0, x_2038);
lean_ctor_set(x_2060, 1, x_2059);
x_2061 = lean_array_push(x_2031, x_2060);
x_2062 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2063 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2063, 0, x_2062);
lean_ctor_set(x_2063, 1, x_2061);
x_2064 = lean_array_push(x_2045, x_2063);
x_2065 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2066 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2066, 0, x_2065);
lean_ctor_set(x_2066, 1, x_2064);
x_2067 = 1;
x_2068 = lean_box(x_2067);
x_2069 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2069, 0, x_2066);
lean_ctor_set(x_2069, 1, x_2068);
lean_ctor_set(x_1903, 1, x_2069);
if (lean_is_scalar(x_2028)) {
 x_2070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2070 = x_2028;
}
lean_ctor_set(x_2070, 0, x_1903);
lean_ctor_set(x_2070, 1, x_2027);
return x_2070;
}
}
else
{
lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; uint8_t x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; 
x_2071 = lean_ctor_get(x_1903, 0);
lean_inc(x_2071);
lean_dec(x_1903);
x_2072 = lean_ctor_get(x_1904, 0);
lean_inc(x_2072);
if (lean_is_exclusive(x_1904)) {
 lean_ctor_release(x_1904, 0);
 lean_ctor_release(x_1904, 1);
 x_2073 = x_1904;
} else {
 lean_dec_ref(x_1904);
 x_2073 = lean_box(0);
}
x_2074 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_1905);
x_2075 = lean_ctor_get(x_2074, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2074, 1);
lean_inc(x_2076);
lean_dec(x_2074);
x_2077 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2076);
lean_dec(x_5);
x_2078 = lean_ctor_get(x_2077, 1);
lean_inc(x_2078);
lean_dec(x_2077);
x_2079 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2078);
x_2080 = lean_ctor_get(x_2079, 1);
lean_inc(x_2080);
if (lean_is_exclusive(x_2079)) {
 lean_ctor_release(x_2079, 0);
 lean_ctor_release(x_2079, 1);
 x_2081 = x_2079;
} else {
 lean_dec_ref(x_2079);
 x_2081 = lean_box(0);
}
x_2082 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2075);
x_2083 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2083, 0, x_2075);
lean_ctor_set(x_2083, 1, x_2082);
x_2084 = l_Array_empty___closed__1;
x_2085 = lean_array_push(x_2084, x_2083);
x_2086 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2087 = lean_array_push(x_2086, x_1896);
x_2088 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2089 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2089, 0, x_2088);
lean_ctor_set(x_2089, 1, x_2087);
x_2090 = lean_array_push(x_2084, x_2089);
x_2091 = l_Lean_nullKind___closed__2;
x_2092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2092, 0, x_2091);
lean_ctor_set(x_2092, 1, x_2090);
x_2093 = lean_array_push(x_2085, x_2092);
x_2094 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2095 = lean_array_push(x_2093, x_2094);
x_2096 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2075);
x_2097 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2097, 0, x_2075);
lean_ctor_set(x_2097, 1, x_2096);
x_2098 = lean_array_push(x_2095, x_2097);
x_2099 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2075);
x_2100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2100, 0, x_2075);
lean_ctor_set(x_2100, 1, x_2099);
x_2101 = lean_array_push(x_2084, x_2100);
lean_inc(x_19);
x_2102 = lean_array_push(x_2084, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2103 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2103 = lean_box(0);
}
if (lean_is_scalar(x_2103)) {
 x_2104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2104 = x_2103;
}
lean_ctor_set(x_2104, 0, x_2091);
lean_ctor_set(x_2104, 1, x_2102);
x_2105 = lean_array_push(x_2101, x_2104);
x_2106 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2107, 0, x_2075);
lean_ctor_set(x_2107, 1, x_2106);
x_2108 = lean_array_push(x_2105, x_2107);
x_2109 = lean_array_push(x_2108, x_2072);
x_2110 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2111, 0, x_2110);
lean_ctor_set(x_2111, 1, x_2109);
x_2112 = lean_array_push(x_2084, x_2111);
x_2113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2113, 0, x_2091);
lean_ctor_set(x_2113, 1, x_2112);
x_2114 = lean_array_push(x_2084, x_2113);
x_2115 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2116, 0, x_2115);
lean_ctor_set(x_2116, 1, x_2114);
x_2117 = lean_array_push(x_2098, x_2116);
x_2118 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2119, 0, x_2118);
lean_ctor_set(x_2119, 1, x_2117);
x_2120 = 1;
x_2121 = lean_box(x_2120);
if (lean_is_scalar(x_2073)) {
 x_2122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2122 = x_2073;
}
lean_ctor_set(x_2122, 0, x_2119);
lean_ctor_set(x_2122, 1, x_2121);
x_2123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2123, 0, x_2071);
lean_ctor_set(x_2123, 1, x_2122);
if (lean_is_scalar(x_2081)) {
 x_2124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2124 = x_2081;
}
lean_ctor_set(x_2124, 0, x_2123);
lean_ctor_set(x_2124, 1, x_2080);
return x_2124;
}
}
}
}
else
{
lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; 
lean_dec(x_233);
lean_inc(x_5);
x_2125 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_2126 = lean_ctor_get(x_2125, 0);
lean_inc(x_2126);
x_2127 = lean_ctor_get(x_2125, 1);
lean_inc(x_2127);
lean_dec(x_2125);
x_2128 = lean_unsigned_to_nat(1u);
x_2129 = lean_nat_add(x_3, x_2128);
lean_dec(x_3);
x_2130 = l_Lean_Elab_Term_mkExplicitBinder(x_2126, x_19);
x_2131 = lean_array_push(x_4, x_2130);
x_3 = x_2129;
x_4 = x_2131;
x_11 = x_2127;
goto _start;
}
}
else
{
lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; 
lean_dec(x_233);
x_2133 = lean_unsigned_to_nat(1u);
x_2134 = lean_nat_add(x_3, x_2133);
lean_dec(x_3);
x_2135 = lean_array_push(x_4, x_19);
x_3 = x_2134;
x_4 = x_2135;
goto _start;
}
}
else
{
lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; 
lean_dec(x_233);
x_2137 = lean_unsigned_to_nat(1u);
x_2138 = lean_nat_add(x_3, x_2137);
lean_dec(x_3);
x_2139 = lean_array_push(x_4, x_19);
x_3 = x_2138;
x_4 = x_2139;
goto _start;
}
}
else
{
lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; 
lean_dec(x_233);
x_2141 = lean_unsigned_to_nat(1u);
x_2142 = lean_nat_add(x_3, x_2141);
lean_dec(x_3);
x_2143 = lean_array_push(x_4, x_19);
x_3 = x_2142;
x_4 = x_2143;
goto _start;
}
}
else
{
lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; 
lean_dec(x_233);
x_2145 = lean_unsigned_to_nat(1u);
x_2146 = lean_nat_add(x_3, x_2145);
lean_dec(x_3);
x_2147 = lean_array_push(x_4, x_19);
x_3 = x_2146;
x_4 = x_2147;
goto _start;
}
}
}
}
}
else
{
lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; uint8_t x_2161; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_inc(x_5);
x_2149 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_2150 = lean_ctor_get(x_2149, 0);
lean_inc(x_2150);
x_2151 = lean_ctor_get(x_2149, 1);
lean_inc(x_2151);
lean_dec(x_2149);
x_2152 = lean_unsigned_to_nat(1u);
x_2153 = lean_nat_add(x_3, x_2152);
lean_dec(x_3);
x_2154 = l_Lean_mkHole(x_19);
lean_inc(x_2150);
x_2155 = l_Lean_Elab_Term_mkExplicitBinder(x_2150, x_2154);
x_2156 = lean_array_push(x_4, x_2155);
lean_inc(x_5);
x_2157 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2153, x_2156, x_5, x_6, x_7, x_8, x_9, x_10, x_2151);
x_2158 = lean_ctor_get(x_2157, 0);
lean_inc(x_2158);
x_2159 = lean_ctor_get(x_2158, 1);
lean_inc(x_2159);
x_2160 = lean_ctor_get(x_2157, 1);
lean_inc(x_2160);
lean_dec(x_2157);
x_2161 = !lean_is_exclusive(x_2158);
if (x_2161 == 0)
{
lean_object* x_2162; uint8_t x_2163; 
x_2162 = lean_ctor_get(x_2158, 1);
lean_dec(x_2162);
x_2163 = !lean_is_exclusive(x_2159);
if (x_2163 == 0)
{
lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; uint8_t x_2172; 
x_2164 = lean_ctor_get(x_2159, 0);
x_2165 = lean_ctor_get(x_2159, 1);
lean_dec(x_2165);
x_2166 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2160);
x_2167 = lean_ctor_get(x_2166, 0);
lean_inc(x_2167);
x_2168 = lean_ctor_get(x_2166, 1);
lean_inc(x_2168);
lean_dec(x_2166);
x_2169 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2168);
lean_dec(x_5);
x_2170 = lean_ctor_get(x_2169, 1);
lean_inc(x_2170);
lean_dec(x_2169);
x_2171 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2170);
x_2172 = !lean_is_exclusive(x_2171);
if (x_2172 == 0)
{
lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; uint8_t x_2195; 
x_2173 = lean_ctor_get(x_2171, 0);
lean_dec(x_2173);
x_2174 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2167);
x_2175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2175, 0, x_2167);
lean_ctor_set(x_2175, 1, x_2174);
x_2176 = l_Array_empty___closed__1;
x_2177 = lean_array_push(x_2176, x_2175);
x_2178 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2179 = lean_array_push(x_2178, x_2150);
x_2180 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2181, 0, x_2180);
lean_ctor_set(x_2181, 1, x_2179);
x_2182 = lean_array_push(x_2176, x_2181);
x_2183 = l_Lean_nullKind___closed__2;
x_2184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2184, 0, x_2183);
lean_ctor_set(x_2184, 1, x_2182);
x_2185 = lean_array_push(x_2177, x_2184);
x_2186 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2187 = lean_array_push(x_2185, x_2186);
x_2188 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2167);
x_2189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2189, 0, x_2167);
lean_ctor_set(x_2189, 1, x_2188);
x_2190 = lean_array_push(x_2187, x_2189);
x_2191 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2167);
x_2192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2192, 0, x_2167);
lean_ctor_set(x_2192, 1, x_2191);
x_2193 = lean_array_push(x_2176, x_2192);
lean_inc(x_19);
x_2194 = lean_array_push(x_2176, x_19);
x_2195 = !lean_is_exclusive(x_19);
if (x_2195 == 0)
{
lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; uint8_t x_2213; lean_object* x_2214; 
x_2196 = lean_ctor_get(x_19, 1);
lean_dec(x_2196);
x_2197 = lean_ctor_get(x_19, 0);
lean_dec(x_2197);
lean_ctor_set(x_19, 1, x_2194);
lean_ctor_set(x_19, 0, x_2183);
x_2198 = lean_array_push(x_2193, x_19);
x_2199 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2200, 0, x_2167);
lean_ctor_set(x_2200, 1, x_2199);
x_2201 = lean_array_push(x_2198, x_2200);
x_2202 = lean_array_push(x_2201, x_2164);
x_2203 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2204, 0, x_2203);
lean_ctor_set(x_2204, 1, x_2202);
x_2205 = lean_array_push(x_2176, x_2204);
x_2206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2206, 0, x_2183);
lean_ctor_set(x_2206, 1, x_2205);
x_2207 = lean_array_push(x_2176, x_2206);
x_2208 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2209, 0, x_2208);
lean_ctor_set(x_2209, 1, x_2207);
x_2210 = lean_array_push(x_2190, x_2209);
x_2211 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2212, 0, x_2211);
lean_ctor_set(x_2212, 1, x_2210);
x_2213 = 1;
x_2214 = lean_box(x_2213);
lean_ctor_set(x_2159, 1, x_2214);
lean_ctor_set(x_2159, 0, x_2212);
lean_ctor_set(x_2171, 0, x_2158);
return x_2171;
}
else
{
lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; uint8_t x_2231; lean_object* x_2232; 
lean_dec(x_19);
x_2215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2215, 0, x_2183);
lean_ctor_set(x_2215, 1, x_2194);
x_2216 = lean_array_push(x_2193, x_2215);
x_2217 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2218, 0, x_2167);
lean_ctor_set(x_2218, 1, x_2217);
x_2219 = lean_array_push(x_2216, x_2218);
x_2220 = lean_array_push(x_2219, x_2164);
x_2221 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2222, 0, x_2221);
lean_ctor_set(x_2222, 1, x_2220);
x_2223 = lean_array_push(x_2176, x_2222);
x_2224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2224, 0, x_2183);
lean_ctor_set(x_2224, 1, x_2223);
x_2225 = lean_array_push(x_2176, x_2224);
x_2226 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2227, 0, x_2226);
lean_ctor_set(x_2227, 1, x_2225);
x_2228 = lean_array_push(x_2190, x_2227);
x_2229 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2230, 0, x_2229);
lean_ctor_set(x_2230, 1, x_2228);
x_2231 = 1;
x_2232 = lean_box(x_2231);
lean_ctor_set(x_2159, 1, x_2232);
lean_ctor_set(x_2159, 0, x_2230);
lean_ctor_set(x_2171, 0, x_2158);
return x_2171;
}
}
else
{
lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; uint8_t x_2272; lean_object* x_2273; lean_object* x_2274; 
x_2233 = lean_ctor_get(x_2171, 1);
lean_inc(x_2233);
lean_dec(x_2171);
x_2234 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2167);
x_2235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2235, 0, x_2167);
lean_ctor_set(x_2235, 1, x_2234);
x_2236 = l_Array_empty___closed__1;
x_2237 = lean_array_push(x_2236, x_2235);
x_2238 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2239 = lean_array_push(x_2238, x_2150);
x_2240 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2241, 0, x_2240);
lean_ctor_set(x_2241, 1, x_2239);
x_2242 = lean_array_push(x_2236, x_2241);
x_2243 = l_Lean_nullKind___closed__2;
x_2244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2244, 0, x_2243);
lean_ctor_set(x_2244, 1, x_2242);
x_2245 = lean_array_push(x_2237, x_2244);
x_2246 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2247 = lean_array_push(x_2245, x_2246);
x_2248 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2167);
x_2249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2249, 0, x_2167);
lean_ctor_set(x_2249, 1, x_2248);
x_2250 = lean_array_push(x_2247, x_2249);
x_2251 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2167);
x_2252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2252, 0, x_2167);
lean_ctor_set(x_2252, 1, x_2251);
x_2253 = lean_array_push(x_2236, x_2252);
lean_inc(x_19);
x_2254 = lean_array_push(x_2236, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2255 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2255 = lean_box(0);
}
if (lean_is_scalar(x_2255)) {
 x_2256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2256 = x_2255;
}
lean_ctor_set(x_2256, 0, x_2243);
lean_ctor_set(x_2256, 1, x_2254);
x_2257 = lean_array_push(x_2253, x_2256);
x_2258 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2259 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2259, 0, x_2167);
lean_ctor_set(x_2259, 1, x_2258);
x_2260 = lean_array_push(x_2257, x_2259);
x_2261 = lean_array_push(x_2260, x_2164);
x_2262 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2263, 0, x_2262);
lean_ctor_set(x_2263, 1, x_2261);
x_2264 = lean_array_push(x_2236, x_2263);
x_2265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2265, 0, x_2243);
lean_ctor_set(x_2265, 1, x_2264);
x_2266 = lean_array_push(x_2236, x_2265);
x_2267 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2268, 0, x_2267);
lean_ctor_set(x_2268, 1, x_2266);
x_2269 = lean_array_push(x_2250, x_2268);
x_2270 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2271, 0, x_2270);
lean_ctor_set(x_2271, 1, x_2269);
x_2272 = 1;
x_2273 = lean_box(x_2272);
lean_ctor_set(x_2159, 1, x_2273);
lean_ctor_set(x_2159, 0, x_2271);
x_2274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2274, 0, x_2158);
lean_ctor_set(x_2274, 1, x_2233);
return x_2274;
}
}
else
{
lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; uint8_t x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; 
x_2275 = lean_ctor_get(x_2159, 0);
lean_inc(x_2275);
lean_dec(x_2159);
x_2276 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2160);
x_2277 = lean_ctor_get(x_2276, 0);
lean_inc(x_2277);
x_2278 = lean_ctor_get(x_2276, 1);
lean_inc(x_2278);
lean_dec(x_2276);
x_2279 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2278);
lean_dec(x_5);
x_2280 = lean_ctor_get(x_2279, 1);
lean_inc(x_2280);
lean_dec(x_2279);
x_2281 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2280);
x_2282 = lean_ctor_get(x_2281, 1);
lean_inc(x_2282);
if (lean_is_exclusive(x_2281)) {
 lean_ctor_release(x_2281, 0);
 lean_ctor_release(x_2281, 1);
 x_2283 = x_2281;
} else {
 lean_dec_ref(x_2281);
 x_2283 = lean_box(0);
}
x_2284 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2277);
x_2285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2285, 0, x_2277);
lean_ctor_set(x_2285, 1, x_2284);
x_2286 = l_Array_empty___closed__1;
x_2287 = lean_array_push(x_2286, x_2285);
x_2288 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2289 = lean_array_push(x_2288, x_2150);
x_2290 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2291, 0, x_2290);
lean_ctor_set(x_2291, 1, x_2289);
x_2292 = lean_array_push(x_2286, x_2291);
x_2293 = l_Lean_nullKind___closed__2;
x_2294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2294, 0, x_2293);
lean_ctor_set(x_2294, 1, x_2292);
x_2295 = lean_array_push(x_2287, x_2294);
x_2296 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2297 = lean_array_push(x_2295, x_2296);
x_2298 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2277);
x_2299 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2299, 0, x_2277);
lean_ctor_set(x_2299, 1, x_2298);
x_2300 = lean_array_push(x_2297, x_2299);
x_2301 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2277);
x_2302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2302, 0, x_2277);
lean_ctor_set(x_2302, 1, x_2301);
x_2303 = lean_array_push(x_2286, x_2302);
lean_inc(x_19);
x_2304 = lean_array_push(x_2286, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2305 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2305 = lean_box(0);
}
if (lean_is_scalar(x_2305)) {
 x_2306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2306 = x_2305;
}
lean_ctor_set(x_2306, 0, x_2293);
lean_ctor_set(x_2306, 1, x_2304);
x_2307 = lean_array_push(x_2303, x_2306);
x_2308 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2309, 0, x_2277);
lean_ctor_set(x_2309, 1, x_2308);
x_2310 = lean_array_push(x_2307, x_2309);
x_2311 = lean_array_push(x_2310, x_2275);
x_2312 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2313, 0, x_2312);
lean_ctor_set(x_2313, 1, x_2311);
x_2314 = lean_array_push(x_2286, x_2313);
x_2315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2315, 0, x_2293);
lean_ctor_set(x_2315, 1, x_2314);
x_2316 = lean_array_push(x_2286, x_2315);
x_2317 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2318, 0, x_2317);
lean_ctor_set(x_2318, 1, x_2316);
x_2319 = lean_array_push(x_2300, x_2318);
x_2320 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2321, 0, x_2320);
lean_ctor_set(x_2321, 1, x_2319);
x_2322 = 1;
x_2323 = lean_box(x_2322);
x_2324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2324, 0, x_2321);
lean_ctor_set(x_2324, 1, x_2323);
lean_ctor_set(x_2158, 1, x_2324);
if (lean_is_scalar(x_2283)) {
 x_2325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2325 = x_2283;
}
lean_ctor_set(x_2325, 0, x_2158);
lean_ctor_set(x_2325, 1, x_2282);
return x_2325;
}
}
else
{
lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; uint8_t x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; 
x_2326 = lean_ctor_get(x_2158, 0);
lean_inc(x_2326);
lean_dec(x_2158);
x_2327 = lean_ctor_get(x_2159, 0);
lean_inc(x_2327);
if (lean_is_exclusive(x_2159)) {
 lean_ctor_release(x_2159, 0);
 lean_ctor_release(x_2159, 1);
 x_2328 = x_2159;
} else {
 lean_dec_ref(x_2159);
 x_2328 = lean_box(0);
}
x_2329 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2160);
x_2330 = lean_ctor_get(x_2329, 0);
lean_inc(x_2330);
x_2331 = lean_ctor_get(x_2329, 1);
lean_inc(x_2331);
lean_dec(x_2329);
x_2332 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2331);
lean_dec(x_5);
x_2333 = lean_ctor_get(x_2332, 1);
lean_inc(x_2333);
lean_dec(x_2332);
x_2334 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2333);
x_2335 = lean_ctor_get(x_2334, 1);
lean_inc(x_2335);
if (lean_is_exclusive(x_2334)) {
 lean_ctor_release(x_2334, 0);
 lean_ctor_release(x_2334, 1);
 x_2336 = x_2334;
} else {
 lean_dec_ref(x_2334);
 x_2336 = lean_box(0);
}
x_2337 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2330);
x_2338 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2338, 0, x_2330);
lean_ctor_set(x_2338, 1, x_2337);
x_2339 = l_Array_empty___closed__1;
x_2340 = lean_array_push(x_2339, x_2338);
x_2341 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2342 = lean_array_push(x_2341, x_2150);
x_2343 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2344, 0, x_2343);
lean_ctor_set(x_2344, 1, x_2342);
x_2345 = lean_array_push(x_2339, x_2344);
x_2346 = l_Lean_nullKind___closed__2;
x_2347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2347, 0, x_2346);
lean_ctor_set(x_2347, 1, x_2345);
x_2348 = lean_array_push(x_2340, x_2347);
x_2349 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2350 = lean_array_push(x_2348, x_2349);
x_2351 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2330);
x_2352 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2352, 0, x_2330);
lean_ctor_set(x_2352, 1, x_2351);
x_2353 = lean_array_push(x_2350, x_2352);
x_2354 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2330);
x_2355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2355, 0, x_2330);
lean_ctor_set(x_2355, 1, x_2354);
x_2356 = lean_array_push(x_2339, x_2355);
lean_inc(x_19);
x_2357 = lean_array_push(x_2339, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2358 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2358 = lean_box(0);
}
if (lean_is_scalar(x_2358)) {
 x_2359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2359 = x_2358;
}
lean_ctor_set(x_2359, 0, x_2346);
lean_ctor_set(x_2359, 1, x_2357);
x_2360 = lean_array_push(x_2356, x_2359);
x_2361 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2362 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2362, 0, x_2330);
lean_ctor_set(x_2362, 1, x_2361);
x_2363 = lean_array_push(x_2360, x_2362);
x_2364 = lean_array_push(x_2363, x_2327);
x_2365 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2366, 0, x_2365);
lean_ctor_set(x_2366, 1, x_2364);
x_2367 = lean_array_push(x_2339, x_2366);
x_2368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2368, 0, x_2346);
lean_ctor_set(x_2368, 1, x_2367);
x_2369 = lean_array_push(x_2339, x_2368);
x_2370 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2371, 0, x_2370);
lean_ctor_set(x_2371, 1, x_2369);
x_2372 = lean_array_push(x_2353, x_2371);
x_2373 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2374, 0, x_2373);
lean_ctor_set(x_2374, 1, x_2372);
x_2375 = 1;
x_2376 = lean_box(x_2375);
if (lean_is_scalar(x_2328)) {
 x_2377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2377 = x_2328;
}
lean_ctor_set(x_2377, 0, x_2374);
lean_ctor_set(x_2377, 1, x_2376);
x_2378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2378, 0, x_2326);
lean_ctor_set(x_2378, 1, x_2377);
if (lean_is_scalar(x_2336)) {
 x_2379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2379 = x_2336;
}
lean_ctor_set(x_2379, 0, x_2378);
lean_ctor_set(x_2379, 1, x_2335);
return x_2379;
}
}
}
else
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; uint8_t x_2392; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_inc(x_5);
x_2380 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_2381 = lean_ctor_get(x_2380, 0);
lean_inc(x_2381);
x_2382 = lean_ctor_get(x_2380, 1);
lean_inc(x_2382);
lean_dec(x_2380);
x_2383 = lean_unsigned_to_nat(1u);
x_2384 = lean_nat_add(x_3, x_2383);
lean_dec(x_3);
x_2385 = l_Lean_mkHole(x_19);
lean_inc(x_2381);
x_2386 = l_Lean_Elab_Term_mkExplicitBinder(x_2381, x_2385);
x_2387 = lean_array_push(x_4, x_2386);
lean_inc(x_5);
x_2388 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2384, x_2387, x_5, x_6, x_7, x_8, x_9, x_10, x_2382);
x_2389 = lean_ctor_get(x_2388, 0);
lean_inc(x_2389);
x_2390 = lean_ctor_get(x_2389, 1);
lean_inc(x_2390);
x_2391 = lean_ctor_get(x_2388, 1);
lean_inc(x_2391);
lean_dec(x_2388);
x_2392 = !lean_is_exclusive(x_2389);
if (x_2392 == 0)
{
lean_object* x_2393; uint8_t x_2394; 
x_2393 = lean_ctor_get(x_2389, 1);
lean_dec(x_2393);
x_2394 = !lean_is_exclusive(x_2390);
if (x_2394 == 0)
{
lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; uint8_t x_2403; 
x_2395 = lean_ctor_get(x_2390, 0);
x_2396 = lean_ctor_get(x_2390, 1);
lean_dec(x_2396);
x_2397 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2391);
x_2398 = lean_ctor_get(x_2397, 0);
lean_inc(x_2398);
x_2399 = lean_ctor_get(x_2397, 1);
lean_inc(x_2399);
lean_dec(x_2397);
x_2400 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2399);
lean_dec(x_5);
x_2401 = lean_ctor_get(x_2400, 1);
lean_inc(x_2401);
lean_dec(x_2400);
x_2402 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2401);
x_2403 = !lean_is_exclusive(x_2402);
if (x_2403 == 0)
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; uint8_t x_2426; 
x_2404 = lean_ctor_get(x_2402, 0);
lean_dec(x_2404);
x_2405 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2398);
x_2406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2406, 0, x_2398);
lean_ctor_set(x_2406, 1, x_2405);
x_2407 = l_Array_empty___closed__1;
x_2408 = lean_array_push(x_2407, x_2406);
x_2409 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2410 = lean_array_push(x_2409, x_2381);
x_2411 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2412, 0, x_2411);
lean_ctor_set(x_2412, 1, x_2410);
x_2413 = lean_array_push(x_2407, x_2412);
x_2414 = l_Lean_nullKind___closed__2;
x_2415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2415, 0, x_2414);
lean_ctor_set(x_2415, 1, x_2413);
x_2416 = lean_array_push(x_2408, x_2415);
x_2417 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2418 = lean_array_push(x_2416, x_2417);
x_2419 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2398);
x_2420 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2420, 0, x_2398);
lean_ctor_set(x_2420, 1, x_2419);
x_2421 = lean_array_push(x_2418, x_2420);
x_2422 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2398);
x_2423 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2423, 0, x_2398);
lean_ctor_set(x_2423, 1, x_2422);
x_2424 = lean_array_push(x_2407, x_2423);
lean_inc(x_19);
x_2425 = lean_array_push(x_2407, x_19);
x_2426 = !lean_is_exclusive(x_19);
if (x_2426 == 0)
{
lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; uint8_t x_2444; lean_object* x_2445; 
x_2427 = lean_ctor_get(x_19, 1);
lean_dec(x_2427);
x_2428 = lean_ctor_get(x_19, 0);
lean_dec(x_2428);
lean_ctor_set(x_19, 1, x_2425);
lean_ctor_set(x_19, 0, x_2414);
x_2429 = lean_array_push(x_2424, x_19);
x_2430 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2431 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2431, 0, x_2398);
lean_ctor_set(x_2431, 1, x_2430);
x_2432 = lean_array_push(x_2429, x_2431);
x_2433 = lean_array_push(x_2432, x_2395);
x_2434 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2435, 0, x_2434);
lean_ctor_set(x_2435, 1, x_2433);
x_2436 = lean_array_push(x_2407, x_2435);
x_2437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2437, 0, x_2414);
lean_ctor_set(x_2437, 1, x_2436);
x_2438 = lean_array_push(x_2407, x_2437);
x_2439 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2440, 0, x_2439);
lean_ctor_set(x_2440, 1, x_2438);
x_2441 = lean_array_push(x_2421, x_2440);
x_2442 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2443, 0, x_2442);
lean_ctor_set(x_2443, 1, x_2441);
x_2444 = 1;
x_2445 = lean_box(x_2444);
lean_ctor_set(x_2390, 1, x_2445);
lean_ctor_set(x_2390, 0, x_2443);
lean_ctor_set(x_2402, 0, x_2389);
return x_2402;
}
else
{
lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; uint8_t x_2462; lean_object* x_2463; 
lean_dec(x_19);
x_2446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2446, 0, x_2414);
lean_ctor_set(x_2446, 1, x_2425);
x_2447 = lean_array_push(x_2424, x_2446);
x_2448 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2449 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2449, 0, x_2398);
lean_ctor_set(x_2449, 1, x_2448);
x_2450 = lean_array_push(x_2447, x_2449);
x_2451 = lean_array_push(x_2450, x_2395);
x_2452 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2453, 0, x_2452);
lean_ctor_set(x_2453, 1, x_2451);
x_2454 = lean_array_push(x_2407, x_2453);
x_2455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2455, 0, x_2414);
lean_ctor_set(x_2455, 1, x_2454);
x_2456 = lean_array_push(x_2407, x_2455);
x_2457 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2458, 0, x_2457);
lean_ctor_set(x_2458, 1, x_2456);
x_2459 = lean_array_push(x_2421, x_2458);
x_2460 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2461, 0, x_2460);
lean_ctor_set(x_2461, 1, x_2459);
x_2462 = 1;
x_2463 = lean_box(x_2462);
lean_ctor_set(x_2390, 1, x_2463);
lean_ctor_set(x_2390, 0, x_2461);
lean_ctor_set(x_2402, 0, x_2389);
return x_2402;
}
}
else
{
lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; uint8_t x_2503; lean_object* x_2504; lean_object* x_2505; 
x_2464 = lean_ctor_get(x_2402, 1);
lean_inc(x_2464);
lean_dec(x_2402);
x_2465 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2398);
x_2466 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2466, 0, x_2398);
lean_ctor_set(x_2466, 1, x_2465);
x_2467 = l_Array_empty___closed__1;
x_2468 = lean_array_push(x_2467, x_2466);
x_2469 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2470 = lean_array_push(x_2469, x_2381);
x_2471 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2472, 0, x_2471);
lean_ctor_set(x_2472, 1, x_2470);
x_2473 = lean_array_push(x_2467, x_2472);
x_2474 = l_Lean_nullKind___closed__2;
x_2475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2475, 0, x_2474);
lean_ctor_set(x_2475, 1, x_2473);
x_2476 = lean_array_push(x_2468, x_2475);
x_2477 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2478 = lean_array_push(x_2476, x_2477);
x_2479 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2398);
x_2480 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2480, 0, x_2398);
lean_ctor_set(x_2480, 1, x_2479);
x_2481 = lean_array_push(x_2478, x_2480);
x_2482 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2398);
x_2483 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2483, 0, x_2398);
lean_ctor_set(x_2483, 1, x_2482);
x_2484 = lean_array_push(x_2467, x_2483);
lean_inc(x_19);
x_2485 = lean_array_push(x_2467, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2486 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2486 = lean_box(0);
}
if (lean_is_scalar(x_2486)) {
 x_2487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2487 = x_2486;
}
lean_ctor_set(x_2487, 0, x_2474);
lean_ctor_set(x_2487, 1, x_2485);
x_2488 = lean_array_push(x_2484, x_2487);
x_2489 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2490 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2490, 0, x_2398);
lean_ctor_set(x_2490, 1, x_2489);
x_2491 = lean_array_push(x_2488, x_2490);
x_2492 = lean_array_push(x_2491, x_2395);
x_2493 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2494, 0, x_2493);
lean_ctor_set(x_2494, 1, x_2492);
x_2495 = lean_array_push(x_2467, x_2494);
x_2496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2496, 0, x_2474);
lean_ctor_set(x_2496, 1, x_2495);
x_2497 = lean_array_push(x_2467, x_2496);
x_2498 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2499, 0, x_2498);
lean_ctor_set(x_2499, 1, x_2497);
x_2500 = lean_array_push(x_2481, x_2499);
x_2501 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2502, 0, x_2501);
lean_ctor_set(x_2502, 1, x_2500);
x_2503 = 1;
x_2504 = lean_box(x_2503);
lean_ctor_set(x_2390, 1, x_2504);
lean_ctor_set(x_2390, 0, x_2502);
x_2505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2505, 0, x_2389);
lean_ctor_set(x_2505, 1, x_2464);
return x_2505;
}
}
else
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; uint8_t x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; 
x_2506 = lean_ctor_get(x_2390, 0);
lean_inc(x_2506);
lean_dec(x_2390);
x_2507 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2391);
x_2508 = lean_ctor_get(x_2507, 0);
lean_inc(x_2508);
x_2509 = lean_ctor_get(x_2507, 1);
lean_inc(x_2509);
lean_dec(x_2507);
x_2510 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2509);
lean_dec(x_5);
x_2511 = lean_ctor_get(x_2510, 1);
lean_inc(x_2511);
lean_dec(x_2510);
x_2512 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2511);
x_2513 = lean_ctor_get(x_2512, 1);
lean_inc(x_2513);
if (lean_is_exclusive(x_2512)) {
 lean_ctor_release(x_2512, 0);
 lean_ctor_release(x_2512, 1);
 x_2514 = x_2512;
} else {
 lean_dec_ref(x_2512);
 x_2514 = lean_box(0);
}
x_2515 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2508);
x_2516 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2516, 0, x_2508);
lean_ctor_set(x_2516, 1, x_2515);
x_2517 = l_Array_empty___closed__1;
x_2518 = lean_array_push(x_2517, x_2516);
x_2519 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2520 = lean_array_push(x_2519, x_2381);
x_2521 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2522, 0, x_2521);
lean_ctor_set(x_2522, 1, x_2520);
x_2523 = lean_array_push(x_2517, x_2522);
x_2524 = l_Lean_nullKind___closed__2;
x_2525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2525, 0, x_2524);
lean_ctor_set(x_2525, 1, x_2523);
x_2526 = lean_array_push(x_2518, x_2525);
x_2527 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2528 = lean_array_push(x_2526, x_2527);
x_2529 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2508);
x_2530 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2530, 0, x_2508);
lean_ctor_set(x_2530, 1, x_2529);
x_2531 = lean_array_push(x_2528, x_2530);
x_2532 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2508);
x_2533 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2533, 0, x_2508);
lean_ctor_set(x_2533, 1, x_2532);
x_2534 = lean_array_push(x_2517, x_2533);
lean_inc(x_19);
x_2535 = lean_array_push(x_2517, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2536 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2536 = lean_box(0);
}
if (lean_is_scalar(x_2536)) {
 x_2537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2537 = x_2536;
}
lean_ctor_set(x_2537, 0, x_2524);
lean_ctor_set(x_2537, 1, x_2535);
x_2538 = lean_array_push(x_2534, x_2537);
x_2539 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2540 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2540, 0, x_2508);
lean_ctor_set(x_2540, 1, x_2539);
x_2541 = lean_array_push(x_2538, x_2540);
x_2542 = lean_array_push(x_2541, x_2506);
x_2543 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2544, 0, x_2543);
lean_ctor_set(x_2544, 1, x_2542);
x_2545 = lean_array_push(x_2517, x_2544);
x_2546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2546, 0, x_2524);
lean_ctor_set(x_2546, 1, x_2545);
x_2547 = lean_array_push(x_2517, x_2546);
x_2548 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2549, 0, x_2548);
lean_ctor_set(x_2549, 1, x_2547);
x_2550 = lean_array_push(x_2531, x_2549);
x_2551 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2552, 0, x_2551);
lean_ctor_set(x_2552, 1, x_2550);
x_2553 = 1;
x_2554 = lean_box(x_2553);
x_2555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2555, 0, x_2552);
lean_ctor_set(x_2555, 1, x_2554);
lean_ctor_set(x_2389, 1, x_2555);
if (lean_is_scalar(x_2514)) {
 x_2556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2556 = x_2514;
}
lean_ctor_set(x_2556, 0, x_2389);
lean_ctor_set(x_2556, 1, x_2513);
return x_2556;
}
}
else
{
lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; uint8_t x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; 
x_2557 = lean_ctor_get(x_2389, 0);
lean_inc(x_2557);
lean_dec(x_2389);
x_2558 = lean_ctor_get(x_2390, 0);
lean_inc(x_2558);
if (lean_is_exclusive(x_2390)) {
 lean_ctor_release(x_2390, 0);
 lean_ctor_release(x_2390, 1);
 x_2559 = x_2390;
} else {
 lean_dec_ref(x_2390);
 x_2559 = lean_box(0);
}
x_2560 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2391);
x_2561 = lean_ctor_get(x_2560, 0);
lean_inc(x_2561);
x_2562 = lean_ctor_get(x_2560, 1);
lean_inc(x_2562);
lean_dec(x_2560);
x_2563 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2562);
lean_dec(x_5);
x_2564 = lean_ctor_get(x_2563, 1);
lean_inc(x_2564);
lean_dec(x_2563);
x_2565 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2564);
x_2566 = lean_ctor_get(x_2565, 1);
lean_inc(x_2566);
if (lean_is_exclusive(x_2565)) {
 lean_ctor_release(x_2565, 0);
 lean_ctor_release(x_2565, 1);
 x_2567 = x_2565;
} else {
 lean_dec_ref(x_2565);
 x_2567 = lean_box(0);
}
x_2568 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2561);
x_2569 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2569, 0, x_2561);
lean_ctor_set(x_2569, 1, x_2568);
x_2570 = l_Array_empty___closed__1;
x_2571 = lean_array_push(x_2570, x_2569);
x_2572 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2573 = lean_array_push(x_2572, x_2381);
x_2574 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2575, 0, x_2574);
lean_ctor_set(x_2575, 1, x_2573);
x_2576 = lean_array_push(x_2570, x_2575);
x_2577 = l_Lean_nullKind___closed__2;
x_2578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2578, 0, x_2577);
lean_ctor_set(x_2578, 1, x_2576);
x_2579 = lean_array_push(x_2571, x_2578);
x_2580 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2581 = lean_array_push(x_2579, x_2580);
x_2582 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2561);
x_2583 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2583, 0, x_2561);
lean_ctor_set(x_2583, 1, x_2582);
x_2584 = lean_array_push(x_2581, x_2583);
x_2585 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2561);
x_2586 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2586, 0, x_2561);
lean_ctor_set(x_2586, 1, x_2585);
x_2587 = lean_array_push(x_2570, x_2586);
lean_inc(x_19);
x_2588 = lean_array_push(x_2570, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2589 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2589 = lean_box(0);
}
if (lean_is_scalar(x_2589)) {
 x_2590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2590 = x_2589;
}
lean_ctor_set(x_2590, 0, x_2577);
lean_ctor_set(x_2590, 1, x_2588);
x_2591 = lean_array_push(x_2587, x_2590);
x_2592 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2593 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2593, 0, x_2561);
lean_ctor_set(x_2593, 1, x_2592);
x_2594 = lean_array_push(x_2591, x_2593);
x_2595 = lean_array_push(x_2594, x_2558);
x_2596 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2597, 0, x_2596);
lean_ctor_set(x_2597, 1, x_2595);
x_2598 = lean_array_push(x_2570, x_2597);
x_2599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2599, 0, x_2577);
lean_ctor_set(x_2599, 1, x_2598);
x_2600 = lean_array_push(x_2570, x_2599);
x_2601 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2602, 0, x_2601);
lean_ctor_set(x_2602, 1, x_2600);
x_2603 = lean_array_push(x_2584, x_2602);
x_2604 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2605, 0, x_2604);
lean_ctor_set(x_2605, 1, x_2603);
x_2606 = 1;
x_2607 = lean_box(x_2606);
if (lean_is_scalar(x_2559)) {
 x_2608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2608 = x_2559;
}
lean_ctor_set(x_2608, 0, x_2605);
lean_ctor_set(x_2608, 1, x_2607);
x_2609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2609, 0, x_2557);
lean_ctor_set(x_2609, 1, x_2608);
if (lean_is_scalar(x_2567)) {
 x_2610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2610 = x_2567;
}
lean_ctor_set(x_2610, 0, x_2609);
lean_ctor_set(x_2610, 1, x_2566);
return x_2610;
}
}
}
else
{
lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; uint8_t x_2623; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_inc(x_5);
x_2611 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_2612 = lean_ctor_get(x_2611, 0);
lean_inc(x_2612);
x_2613 = lean_ctor_get(x_2611, 1);
lean_inc(x_2613);
lean_dec(x_2611);
x_2614 = lean_unsigned_to_nat(1u);
x_2615 = lean_nat_add(x_3, x_2614);
lean_dec(x_3);
x_2616 = l_Lean_mkHole(x_19);
lean_inc(x_2612);
x_2617 = l_Lean_Elab_Term_mkExplicitBinder(x_2612, x_2616);
x_2618 = lean_array_push(x_4, x_2617);
lean_inc(x_5);
x_2619 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2615, x_2618, x_5, x_6, x_7, x_8, x_9, x_10, x_2613);
x_2620 = lean_ctor_get(x_2619, 0);
lean_inc(x_2620);
x_2621 = lean_ctor_get(x_2620, 1);
lean_inc(x_2621);
x_2622 = lean_ctor_get(x_2619, 1);
lean_inc(x_2622);
lean_dec(x_2619);
x_2623 = !lean_is_exclusive(x_2620);
if (x_2623 == 0)
{
lean_object* x_2624; uint8_t x_2625; 
x_2624 = lean_ctor_get(x_2620, 1);
lean_dec(x_2624);
x_2625 = !lean_is_exclusive(x_2621);
if (x_2625 == 0)
{
lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; uint8_t x_2634; 
x_2626 = lean_ctor_get(x_2621, 0);
x_2627 = lean_ctor_get(x_2621, 1);
lean_dec(x_2627);
x_2628 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2622);
x_2629 = lean_ctor_get(x_2628, 0);
lean_inc(x_2629);
x_2630 = lean_ctor_get(x_2628, 1);
lean_inc(x_2630);
lean_dec(x_2628);
x_2631 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2630);
lean_dec(x_5);
x_2632 = lean_ctor_get(x_2631, 1);
lean_inc(x_2632);
lean_dec(x_2631);
x_2633 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2632);
x_2634 = !lean_is_exclusive(x_2633);
if (x_2634 == 0)
{
lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; uint8_t x_2657; 
x_2635 = lean_ctor_get(x_2633, 0);
lean_dec(x_2635);
x_2636 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2629);
x_2637 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2637, 0, x_2629);
lean_ctor_set(x_2637, 1, x_2636);
x_2638 = l_Array_empty___closed__1;
x_2639 = lean_array_push(x_2638, x_2637);
x_2640 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2641 = lean_array_push(x_2640, x_2612);
x_2642 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2643, 0, x_2642);
lean_ctor_set(x_2643, 1, x_2641);
x_2644 = lean_array_push(x_2638, x_2643);
x_2645 = l_Lean_nullKind___closed__2;
x_2646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2646, 0, x_2645);
lean_ctor_set(x_2646, 1, x_2644);
x_2647 = lean_array_push(x_2639, x_2646);
x_2648 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2649 = lean_array_push(x_2647, x_2648);
x_2650 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2629);
x_2651 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2651, 0, x_2629);
lean_ctor_set(x_2651, 1, x_2650);
x_2652 = lean_array_push(x_2649, x_2651);
x_2653 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2629);
x_2654 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2654, 0, x_2629);
lean_ctor_set(x_2654, 1, x_2653);
x_2655 = lean_array_push(x_2638, x_2654);
lean_inc(x_19);
x_2656 = lean_array_push(x_2638, x_19);
x_2657 = !lean_is_exclusive(x_19);
if (x_2657 == 0)
{
lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; uint8_t x_2675; lean_object* x_2676; 
x_2658 = lean_ctor_get(x_19, 1);
lean_dec(x_2658);
x_2659 = lean_ctor_get(x_19, 0);
lean_dec(x_2659);
lean_ctor_set(x_19, 1, x_2656);
lean_ctor_set(x_19, 0, x_2645);
x_2660 = lean_array_push(x_2655, x_19);
x_2661 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2662 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2662, 0, x_2629);
lean_ctor_set(x_2662, 1, x_2661);
x_2663 = lean_array_push(x_2660, x_2662);
x_2664 = lean_array_push(x_2663, x_2626);
x_2665 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2666 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2666, 0, x_2665);
lean_ctor_set(x_2666, 1, x_2664);
x_2667 = lean_array_push(x_2638, x_2666);
x_2668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2668, 0, x_2645);
lean_ctor_set(x_2668, 1, x_2667);
x_2669 = lean_array_push(x_2638, x_2668);
x_2670 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2671, 0, x_2670);
lean_ctor_set(x_2671, 1, x_2669);
x_2672 = lean_array_push(x_2652, x_2671);
x_2673 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2674, 0, x_2673);
lean_ctor_set(x_2674, 1, x_2672);
x_2675 = 1;
x_2676 = lean_box(x_2675);
lean_ctor_set(x_2621, 1, x_2676);
lean_ctor_set(x_2621, 0, x_2674);
lean_ctor_set(x_2633, 0, x_2620);
return x_2633;
}
else
{
lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; uint8_t x_2693; lean_object* x_2694; 
lean_dec(x_19);
x_2677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2677, 0, x_2645);
lean_ctor_set(x_2677, 1, x_2656);
x_2678 = lean_array_push(x_2655, x_2677);
x_2679 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2680 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2680, 0, x_2629);
lean_ctor_set(x_2680, 1, x_2679);
x_2681 = lean_array_push(x_2678, x_2680);
x_2682 = lean_array_push(x_2681, x_2626);
x_2683 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2684, 0, x_2683);
lean_ctor_set(x_2684, 1, x_2682);
x_2685 = lean_array_push(x_2638, x_2684);
x_2686 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2686, 0, x_2645);
lean_ctor_set(x_2686, 1, x_2685);
x_2687 = lean_array_push(x_2638, x_2686);
x_2688 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2689, 0, x_2688);
lean_ctor_set(x_2689, 1, x_2687);
x_2690 = lean_array_push(x_2652, x_2689);
x_2691 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2692, 0, x_2691);
lean_ctor_set(x_2692, 1, x_2690);
x_2693 = 1;
x_2694 = lean_box(x_2693);
lean_ctor_set(x_2621, 1, x_2694);
lean_ctor_set(x_2621, 0, x_2692);
lean_ctor_set(x_2633, 0, x_2620);
return x_2633;
}
}
else
{
lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; uint8_t x_2734; lean_object* x_2735; lean_object* x_2736; 
x_2695 = lean_ctor_get(x_2633, 1);
lean_inc(x_2695);
lean_dec(x_2633);
x_2696 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2629);
x_2697 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2697, 0, x_2629);
lean_ctor_set(x_2697, 1, x_2696);
x_2698 = l_Array_empty___closed__1;
x_2699 = lean_array_push(x_2698, x_2697);
x_2700 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2701 = lean_array_push(x_2700, x_2612);
x_2702 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2703, 0, x_2702);
lean_ctor_set(x_2703, 1, x_2701);
x_2704 = lean_array_push(x_2698, x_2703);
x_2705 = l_Lean_nullKind___closed__2;
x_2706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2706, 0, x_2705);
lean_ctor_set(x_2706, 1, x_2704);
x_2707 = lean_array_push(x_2699, x_2706);
x_2708 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2709 = lean_array_push(x_2707, x_2708);
x_2710 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2629);
x_2711 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2711, 0, x_2629);
lean_ctor_set(x_2711, 1, x_2710);
x_2712 = lean_array_push(x_2709, x_2711);
x_2713 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2629);
x_2714 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2714, 0, x_2629);
lean_ctor_set(x_2714, 1, x_2713);
x_2715 = lean_array_push(x_2698, x_2714);
lean_inc(x_19);
x_2716 = lean_array_push(x_2698, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2717 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2717 = lean_box(0);
}
if (lean_is_scalar(x_2717)) {
 x_2718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2718 = x_2717;
}
lean_ctor_set(x_2718, 0, x_2705);
lean_ctor_set(x_2718, 1, x_2716);
x_2719 = lean_array_push(x_2715, x_2718);
x_2720 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2721 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2721, 0, x_2629);
lean_ctor_set(x_2721, 1, x_2720);
x_2722 = lean_array_push(x_2719, x_2721);
x_2723 = lean_array_push(x_2722, x_2626);
x_2724 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2725, 0, x_2724);
lean_ctor_set(x_2725, 1, x_2723);
x_2726 = lean_array_push(x_2698, x_2725);
x_2727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2727, 0, x_2705);
lean_ctor_set(x_2727, 1, x_2726);
x_2728 = lean_array_push(x_2698, x_2727);
x_2729 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2730, 0, x_2729);
lean_ctor_set(x_2730, 1, x_2728);
x_2731 = lean_array_push(x_2712, x_2730);
x_2732 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2733, 0, x_2732);
lean_ctor_set(x_2733, 1, x_2731);
x_2734 = 1;
x_2735 = lean_box(x_2734);
lean_ctor_set(x_2621, 1, x_2735);
lean_ctor_set(x_2621, 0, x_2733);
x_2736 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2736, 0, x_2620);
lean_ctor_set(x_2736, 1, x_2695);
return x_2736;
}
}
else
{
lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; lean_object* x_2783; uint8_t x_2784; lean_object* x_2785; lean_object* x_2786; lean_object* x_2787; 
x_2737 = lean_ctor_get(x_2621, 0);
lean_inc(x_2737);
lean_dec(x_2621);
x_2738 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2622);
x_2739 = lean_ctor_get(x_2738, 0);
lean_inc(x_2739);
x_2740 = lean_ctor_get(x_2738, 1);
lean_inc(x_2740);
lean_dec(x_2738);
x_2741 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2740);
lean_dec(x_5);
x_2742 = lean_ctor_get(x_2741, 1);
lean_inc(x_2742);
lean_dec(x_2741);
x_2743 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2742);
x_2744 = lean_ctor_get(x_2743, 1);
lean_inc(x_2744);
if (lean_is_exclusive(x_2743)) {
 lean_ctor_release(x_2743, 0);
 lean_ctor_release(x_2743, 1);
 x_2745 = x_2743;
} else {
 lean_dec_ref(x_2743);
 x_2745 = lean_box(0);
}
x_2746 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2739);
x_2747 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2747, 0, x_2739);
lean_ctor_set(x_2747, 1, x_2746);
x_2748 = l_Array_empty___closed__1;
x_2749 = lean_array_push(x_2748, x_2747);
x_2750 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2751 = lean_array_push(x_2750, x_2612);
x_2752 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2753, 0, x_2752);
lean_ctor_set(x_2753, 1, x_2751);
x_2754 = lean_array_push(x_2748, x_2753);
x_2755 = l_Lean_nullKind___closed__2;
x_2756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2756, 0, x_2755);
lean_ctor_set(x_2756, 1, x_2754);
x_2757 = lean_array_push(x_2749, x_2756);
x_2758 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2759 = lean_array_push(x_2757, x_2758);
x_2760 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2739);
x_2761 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2761, 0, x_2739);
lean_ctor_set(x_2761, 1, x_2760);
x_2762 = lean_array_push(x_2759, x_2761);
x_2763 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2739);
x_2764 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2764, 0, x_2739);
lean_ctor_set(x_2764, 1, x_2763);
x_2765 = lean_array_push(x_2748, x_2764);
lean_inc(x_19);
x_2766 = lean_array_push(x_2748, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2767 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2767 = lean_box(0);
}
if (lean_is_scalar(x_2767)) {
 x_2768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2768 = x_2767;
}
lean_ctor_set(x_2768, 0, x_2755);
lean_ctor_set(x_2768, 1, x_2766);
x_2769 = lean_array_push(x_2765, x_2768);
x_2770 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2771 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2771, 0, x_2739);
lean_ctor_set(x_2771, 1, x_2770);
x_2772 = lean_array_push(x_2769, x_2771);
x_2773 = lean_array_push(x_2772, x_2737);
x_2774 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2775, 0, x_2774);
lean_ctor_set(x_2775, 1, x_2773);
x_2776 = lean_array_push(x_2748, x_2775);
x_2777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2777, 0, x_2755);
lean_ctor_set(x_2777, 1, x_2776);
x_2778 = lean_array_push(x_2748, x_2777);
x_2779 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2780, 0, x_2779);
lean_ctor_set(x_2780, 1, x_2778);
x_2781 = lean_array_push(x_2762, x_2780);
x_2782 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2783, 0, x_2782);
lean_ctor_set(x_2783, 1, x_2781);
x_2784 = 1;
x_2785 = lean_box(x_2784);
x_2786 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2786, 0, x_2783);
lean_ctor_set(x_2786, 1, x_2785);
lean_ctor_set(x_2620, 1, x_2786);
if (lean_is_scalar(x_2745)) {
 x_2787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2787 = x_2745;
}
lean_ctor_set(x_2787, 0, x_2620);
lean_ctor_set(x_2787, 1, x_2744);
return x_2787;
}
}
else
{
lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; lean_object* x_2802; lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; uint8_t x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; 
x_2788 = lean_ctor_get(x_2620, 0);
lean_inc(x_2788);
lean_dec(x_2620);
x_2789 = lean_ctor_get(x_2621, 0);
lean_inc(x_2789);
if (lean_is_exclusive(x_2621)) {
 lean_ctor_release(x_2621, 0);
 lean_ctor_release(x_2621, 1);
 x_2790 = x_2621;
} else {
 lean_dec_ref(x_2621);
 x_2790 = lean_box(0);
}
x_2791 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2622);
x_2792 = lean_ctor_get(x_2791, 0);
lean_inc(x_2792);
x_2793 = lean_ctor_get(x_2791, 1);
lean_inc(x_2793);
lean_dec(x_2791);
x_2794 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2793);
lean_dec(x_5);
x_2795 = lean_ctor_get(x_2794, 1);
lean_inc(x_2795);
lean_dec(x_2794);
x_2796 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2795);
x_2797 = lean_ctor_get(x_2796, 1);
lean_inc(x_2797);
if (lean_is_exclusive(x_2796)) {
 lean_ctor_release(x_2796, 0);
 lean_ctor_release(x_2796, 1);
 x_2798 = x_2796;
} else {
 lean_dec_ref(x_2796);
 x_2798 = lean_box(0);
}
x_2799 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2792);
x_2800 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2800, 0, x_2792);
lean_ctor_set(x_2800, 1, x_2799);
x_2801 = l_Array_empty___closed__1;
x_2802 = lean_array_push(x_2801, x_2800);
x_2803 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2804 = lean_array_push(x_2803, x_2612);
x_2805 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2806, 0, x_2805);
lean_ctor_set(x_2806, 1, x_2804);
x_2807 = lean_array_push(x_2801, x_2806);
x_2808 = l_Lean_nullKind___closed__2;
x_2809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2809, 0, x_2808);
lean_ctor_set(x_2809, 1, x_2807);
x_2810 = lean_array_push(x_2802, x_2809);
x_2811 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2812 = lean_array_push(x_2810, x_2811);
x_2813 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2792);
x_2814 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2814, 0, x_2792);
lean_ctor_set(x_2814, 1, x_2813);
x_2815 = lean_array_push(x_2812, x_2814);
x_2816 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2792);
x_2817 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2817, 0, x_2792);
lean_ctor_set(x_2817, 1, x_2816);
x_2818 = lean_array_push(x_2801, x_2817);
lean_inc(x_19);
x_2819 = lean_array_push(x_2801, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2820 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2820 = lean_box(0);
}
if (lean_is_scalar(x_2820)) {
 x_2821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2821 = x_2820;
}
lean_ctor_set(x_2821, 0, x_2808);
lean_ctor_set(x_2821, 1, x_2819);
x_2822 = lean_array_push(x_2818, x_2821);
x_2823 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2824 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2824, 0, x_2792);
lean_ctor_set(x_2824, 1, x_2823);
x_2825 = lean_array_push(x_2822, x_2824);
x_2826 = lean_array_push(x_2825, x_2789);
x_2827 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2828, 0, x_2827);
lean_ctor_set(x_2828, 1, x_2826);
x_2829 = lean_array_push(x_2801, x_2828);
x_2830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2830, 0, x_2808);
lean_ctor_set(x_2830, 1, x_2829);
x_2831 = lean_array_push(x_2801, x_2830);
x_2832 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2833, 0, x_2832);
lean_ctor_set(x_2833, 1, x_2831);
x_2834 = lean_array_push(x_2815, x_2833);
x_2835 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2836, 0, x_2835);
lean_ctor_set(x_2836, 1, x_2834);
x_2837 = 1;
x_2838 = lean_box(x_2837);
if (lean_is_scalar(x_2790)) {
 x_2839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2839 = x_2790;
}
lean_ctor_set(x_2839, 0, x_2836);
lean_ctor_set(x_2839, 1, x_2838);
x_2840 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2840, 0, x_2788);
lean_ctor_set(x_2840, 1, x_2839);
if (lean_is_scalar(x_2798)) {
 x_2841 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2841 = x_2798;
}
lean_ctor_set(x_2841, 0, x_2840);
lean_ctor_set(x_2841, 1, x_2797);
return x_2841;
}
}
}
else
{
lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; uint8_t x_2854; 
lean_dec(x_229);
lean_dec(x_228);
lean_inc(x_5);
x_2842 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_2843 = lean_ctor_get(x_2842, 0);
lean_inc(x_2843);
x_2844 = lean_ctor_get(x_2842, 1);
lean_inc(x_2844);
lean_dec(x_2842);
x_2845 = lean_unsigned_to_nat(1u);
x_2846 = lean_nat_add(x_3, x_2845);
lean_dec(x_3);
x_2847 = l_Lean_mkHole(x_19);
lean_inc(x_2843);
x_2848 = l_Lean_Elab_Term_mkExplicitBinder(x_2843, x_2847);
x_2849 = lean_array_push(x_4, x_2848);
lean_inc(x_5);
x_2850 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2846, x_2849, x_5, x_6, x_7, x_8, x_9, x_10, x_2844);
x_2851 = lean_ctor_get(x_2850, 0);
lean_inc(x_2851);
x_2852 = lean_ctor_get(x_2851, 1);
lean_inc(x_2852);
x_2853 = lean_ctor_get(x_2850, 1);
lean_inc(x_2853);
lean_dec(x_2850);
x_2854 = !lean_is_exclusive(x_2851);
if (x_2854 == 0)
{
lean_object* x_2855; uint8_t x_2856; 
x_2855 = lean_ctor_get(x_2851, 1);
lean_dec(x_2855);
x_2856 = !lean_is_exclusive(x_2852);
if (x_2856 == 0)
{
lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; uint8_t x_2865; 
x_2857 = lean_ctor_get(x_2852, 0);
x_2858 = lean_ctor_get(x_2852, 1);
lean_dec(x_2858);
x_2859 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2853);
x_2860 = lean_ctor_get(x_2859, 0);
lean_inc(x_2860);
x_2861 = lean_ctor_get(x_2859, 1);
lean_inc(x_2861);
lean_dec(x_2859);
x_2862 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2861);
lean_dec(x_5);
x_2863 = lean_ctor_get(x_2862, 1);
lean_inc(x_2863);
lean_dec(x_2862);
x_2864 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2863);
x_2865 = !lean_is_exclusive(x_2864);
if (x_2865 == 0)
{
lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; uint8_t x_2888; 
x_2866 = lean_ctor_get(x_2864, 0);
lean_dec(x_2866);
x_2867 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2860);
x_2868 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2868, 0, x_2860);
lean_ctor_set(x_2868, 1, x_2867);
x_2869 = l_Array_empty___closed__1;
x_2870 = lean_array_push(x_2869, x_2868);
x_2871 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2872 = lean_array_push(x_2871, x_2843);
x_2873 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2874, 0, x_2873);
lean_ctor_set(x_2874, 1, x_2872);
x_2875 = lean_array_push(x_2869, x_2874);
x_2876 = l_Lean_nullKind___closed__2;
x_2877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2877, 0, x_2876);
lean_ctor_set(x_2877, 1, x_2875);
x_2878 = lean_array_push(x_2870, x_2877);
x_2879 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2880 = lean_array_push(x_2878, x_2879);
x_2881 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2860);
x_2882 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2882, 0, x_2860);
lean_ctor_set(x_2882, 1, x_2881);
x_2883 = lean_array_push(x_2880, x_2882);
x_2884 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2860);
x_2885 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2885, 0, x_2860);
lean_ctor_set(x_2885, 1, x_2884);
x_2886 = lean_array_push(x_2869, x_2885);
lean_inc(x_19);
x_2887 = lean_array_push(x_2869, x_19);
x_2888 = !lean_is_exclusive(x_19);
if (x_2888 == 0)
{
lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; uint8_t x_2906; lean_object* x_2907; 
x_2889 = lean_ctor_get(x_19, 1);
lean_dec(x_2889);
x_2890 = lean_ctor_get(x_19, 0);
lean_dec(x_2890);
lean_ctor_set(x_19, 1, x_2887);
lean_ctor_set(x_19, 0, x_2876);
x_2891 = lean_array_push(x_2886, x_19);
x_2892 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2893 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2893, 0, x_2860);
lean_ctor_set(x_2893, 1, x_2892);
x_2894 = lean_array_push(x_2891, x_2893);
x_2895 = lean_array_push(x_2894, x_2857);
x_2896 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2897 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2897, 0, x_2896);
lean_ctor_set(x_2897, 1, x_2895);
x_2898 = lean_array_push(x_2869, x_2897);
x_2899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2899, 0, x_2876);
lean_ctor_set(x_2899, 1, x_2898);
x_2900 = lean_array_push(x_2869, x_2899);
x_2901 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2902, 0, x_2901);
lean_ctor_set(x_2902, 1, x_2900);
x_2903 = lean_array_push(x_2883, x_2902);
x_2904 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2905 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2905, 0, x_2904);
lean_ctor_set(x_2905, 1, x_2903);
x_2906 = 1;
x_2907 = lean_box(x_2906);
lean_ctor_set(x_2852, 1, x_2907);
lean_ctor_set(x_2852, 0, x_2905);
lean_ctor_set(x_2864, 0, x_2851);
return x_2864;
}
else
{
lean_object* x_2908; lean_object* x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; uint8_t x_2924; lean_object* x_2925; 
lean_dec(x_19);
x_2908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2908, 0, x_2876);
lean_ctor_set(x_2908, 1, x_2887);
x_2909 = lean_array_push(x_2886, x_2908);
x_2910 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2911 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2911, 0, x_2860);
lean_ctor_set(x_2911, 1, x_2910);
x_2912 = lean_array_push(x_2909, x_2911);
x_2913 = lean_array_push(x_2912, x_2857);
x_2914 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2915, 0, x_2914);
lean_ctor_set(x_2915, 1, x_2913);
x_2916 = lean_array_push(x_2869, x_2915);
x_2917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2917, 0, x_2876);
lean_ctor_set(x_2917, 1, x_2916);
x_2918 = lean_array_push(x_2869, x_2917);
x_2919 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2920 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2920, 0, x_2919);
lean_ctor_set(x_2920, 1, x_2918);
x_2921 = lean_array_push(x_2883, x_2920);
x_2922 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2923, 0, x_2922);
lean_ctor_set(x_2923, 1, x_2921);
x_2924 = 1;
x_2925 = lean_box(x_2924);
lean_ctor_set(x_2852, 1, x_2925);
lean_ctor_set(x_2852, 0, x_2923);
lean_ctor_set(x_2864, 0, x_2851);
return x_2864;
}
}
else
{
lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; uint8_t x_2965; lean_object* x_2966; lean_object* x_2967; 
x_2926 = lean_ctor_get(x_2864, 1);
lean_inc(x_2926);
lean_dec(x_2864);
x_2927 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2860);
x_2928 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2928, 0, x_2860);
lean_ctor_set(x_2928, 1, x_2927);
x_2929 = l_Array_empty___closed__1;
x_2930 = lean_array_push(x_2929, x_2928);
x_2931 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2932 = lean_array_push(x_2931, x_2843);
x_2933 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2934 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2934, 0, x_2933);
lean_ctor_set(x_2934, 1, x_2932);
x_2935 = lean_array_push(x_2929, x_2934);
x_2936 = l_Lean_nullKind___closed__2;
x_2937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2937, 0, x_2936);
lean_ctor_set(x_2937, 1, x_2935);
x_2938 = lean_array_push(x_2930, x_2937);
x_2939 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2940 = lean_array_push(x_2938, x_2939);
x_2941 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2860);
x_2942 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2942, 0, x_2860);
lean_ctor_set(x_2942, 1, x_2941);
x_2943 = lean_array_push(x_2940, x_2942);
x_2944 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2860);
x_2945 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2945, 0, x_2860);
lean_ctor_set(x_2945, 1, x_2944);
x_2946 = lean_array_push(x_2929, x_2945);
lean_inc(x_19);
x_2947 = lean_array_push(x_2929, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2948 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2948 = lean_box(0);
}
if (lean_is_scalar(x_2948)) {
 x_2949 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2949 = x_2948;
}
lean_ctor_set(x_2949, 0, x_2936);
lean_ctor_set(x_2949, 1, x_2947);
x_2950 = lean_array_push(x_2946, x_2949);
x_2951 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_2952 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2952, 0, x_2860);
lean_ctor_set(x_2952, 1, x_2951);
x_2953 = lean_array_push(x_2950, x_2952);
x_2954 = lean_array_push(x_2953, x_2857);
x_2955 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_2956 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2956, 0, x_2955);
lean_ctor_set(x_2956, 1, x_2954);
x_2957 = lean_array_push(x_2929, x_2956);
x_2958 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2958, 0, x_2936);
lean_ctor_set(x_2958, 1, x_2957);
x_2959 = lean_array_push(x_2929, x_2958);
x_2960 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_2961 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2961, 0, x_2960);
lean_ctor_set(x_2961, 1, x_2959);
x_2962 = lean_array_push(x_2943, x_2961);
x_2963 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_2964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2964, 0, x_2963);
lean_ctor_set(x_2964, 1, x_2962);
x_2965 = 1;
x_2966 = lean_box(x_2965);
lean_ctor_set(x_2852, 1, x_2966);
lean_ctor_set(x_2852, 0, x_2964);
x_2967 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2967, 0, x_2851);
lean_ctor_set(x_2967, 1, x_2926);
return x_2967;
}
}
else
{
lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; uint8_t x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; 
x_2968 = lean_ctor_get(x_2852, 0);
lean_inc(x_2968);
lean_dec(x_2852);
x_2969 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2853);
x_2970 = lean_ctor_get(x_2969, 0);
lean_inc(x_2970);
x_2971 = lean_ctor_get(x_2969, 1);
lean_inc(x_2971);
lean_dec(x_2969);
x_2972 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_2971);
lean_dec(x_5);
x_2973 = lean_ctor_get(x_2972, 1);
lean_inc(x_2973);
lean_dec(x_2972);
x_2974 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_2973);
x_2975 = lean_ctor_get(x_2974, 1);
lean_inc(x_2975);
if (lean_is_exclusive(x_2974)) {
 lean_ctor_release(x_2974, 0);
 lean_ctor_release(x_2974, 1);
 x_2976 = x_2974;
} else {
 lean_dec_ref(x_2974);
 x_2976 = lean_box(0);
}
x_2977 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_2970);
x_2978 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2978, 0, x_2970);
lean_ctor_set(x_2978, 1, x_2977);
x_2979 = l_Array_empty___closed__1;
x_2980 = lean_array_push(x_2979, x_2978);
x_2981 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_2982 = lean_array_push(x_2981, x_2843);
x_2983 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_2984 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2984, 0, x_2983);
lean_ctor_set(x_2984, 1, x_2982);
x_2985 = lean_array_push(x_2979, x_2984);
x_2986 = l_Lean_nullKind___closed__2;
x_2987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2987, 0, x_2986);
lean_ctor_set(x_2987, 1, x_2985);
x_2988 = lean_array_push(x_2980, x_2987);
x_2989 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_2990 = lean_array_push(x_2988, x_2989);
x_2991 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_2970);
x_2992 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2992, 0, x_2970);
lean_ctor_set(x_2992, 1, x_2991);
x_2993 = lean_array_push(x_2990, x_2992);
x_2994 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_2970);
x_2995 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2995, 0, x_2970);
lean_ctor_set(x_2995, 1, x_2994);
x_2996 = lean_array_push(x_2979, x_2995);
lean_inc(x_19);
x_2997 = lean_array_push(x_2979, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_2998 = x_19;
} else {
 lean_dec_ref(x_19);
 x_2998 = lean_box(0);
}
if (lean_is_scalar(x_2998)) {
 x_2999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2999 = x_2998;
}
lean_ctor_set(x_2999, 0, x_2986);
lean_ctor_set(x_2999, 1, x_2997);
x_3000 = lean_array_push(x_2996, x_2999);
x_3001 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3002 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3002, 0, x_2970);
lean_ctor_set(x_3002, 1, x_3001);
x_3003 = lean_array_push(x_3000, x_3002);
x_3004 = lean_array_push(x_3003, x_2968);
x_3005 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3006, 0, x_3005);
lean_ctor_set(x_3006, 1, x_3004);
x_3007 = lean_array_push(x_2979, x_3006);
x_3008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3008, 0, x_2986);
lean_ctor_set(x_3008, 1, x_3007);
x_3009 = lean_array_push(x_2979, x_3008);
x_3010 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3011, 0, x_3010);
lean_ctor_set(x_3011, 1, x_3009);
x_3012 = lean_array_push(x_2993, x_3011);
x_3013 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3014, 0, x_3013);
lean_ctor_set(x_3014, 1, x_3012);
x_3015 = 1;
x_3016 = lean_box(x_3015);
x_3017 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3017, 0, x_3014);
lean_ctor_set(x_3017, 1, x_3016);
lean_ctor_set(x_2851, 1, x_3017);
if (lean_is_scalar(x_2976)) {
 x_3018 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3018 = x_2976;
}
lean_ctor_set(x_3018, 0, x_2851);
lean_ctor_set(x_3018, 1, x_2975);
return x_3018;
}
}
else
{
lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; lean_object* x_3067; uint8_t x_3068; lean_object* x_3069; lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; 
x_3019 = lean_ctor_get(x_2851, 0);
lean_inc(x_3019);
lean_dec(x_2851);
x_3020 = lean_ctor_get(x_2852, 0);
lean_inc(x_3020);
if (lean_is_exclusive(x_2852)) {
 lean_ctor_release(x_2852, 0);
 lean_ctor_release(x_2852, 1);
 x_3021 = x_2852;
} else {
 lean_dec_ref(x_2852);
 x_3021 = lean_box(0);
}
x_3022 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_2853);
x_3023 = lean_ctor_get(x_3022, 0);
lean_inc(x_3023);
x_3024 = lean_ctor_get(x_3022, 1);
lean_inc(x_3024);
lean_dec(x_3022);
x_3025 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3024);
lean_dec(x_5);
x_3026 = lean_ctor_get(x_3025, 1);
lean_inc(x_3026);
lean_dec(x_3025);
x_3027 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3026);
x_3028 = lean_ctor_get(x_3027, 1);
lean_inc(x_3028);
if (lean_is_exclusive(x_3027)) {
 lean_ctor_release(x_3027, 0);
 lean_ctor_release(x_3027, 1);
 x_3029 = x_3027;
} else {
 lean_dec_ref(x_3027);
 x_3029 = lean_box(0);
}
x_3030 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3023);
x_3031 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3031, 0, x_3023);
lean_ctor_set(x_3031, 1, x_3030);
x_3032 = l_Array_empty___closed__1;
x_3033 = lean_array_push(x_3032, x_3031);
x_3034 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3035 = lean_array_push(x_3034, x_2843);
x_3036 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3037, 0, x_3036);
lean_ctor_set(x_3037, 1, x_3035);
x_3038 = lean_array_push(x_3032, x_3037);
x_3039 = l_Lean_nullKind___closed__2;
x_3040 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3040, 0, x_3039);
lean_ctor_set(x_3040, 1, x_3038);
x_3041 = lean_array_push(x_3033, x_3040);
x_3042 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3043 = lean_array_push(x_3041, x_3042);
x_3044 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3023);
x_3045 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3045, 0, x_3023);
lean_ctor_set(x_3045, 1, x_3044);
x_3046 = lean_array_push(x_3043, x_3045);
x_3047 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3023);
x_3048 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3048, 0, x_3023);
lean_ctor_set(x_3048, 1, x_3047);
x_3049 = lean_array_push(x_3032, x_3048);
lean_inc(x_19);
x_3050 = lean_array_push(x_3032, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3051 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3051 = lean_box(0);
}
if (lean_is_scalar(x_3051)) {
 x_3052 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3052 = x_3051;
}
lean_ctor_set(x_3052, 0, x_3039);
lean_ctor_set(x_3052, 1, x_3050);
x_3053 = lean_array_push(x_3049, x_3052);
x_3054 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3055 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3055, 0, x_3023);
lean_ctor_set(x_3055, 1, x_3054);
x_3056 = lean_array_push(x_3053, x_3055);
x_3057 = lean_array_push(x_3056, x_3020);
x_3058 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3059, 0, x_3058);
lean_ctor_set(x_3059, 1, x_3057);
x_3060 = lean_array_push(x_3032, x_3059);
x_3061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3061, 0, x_3039);
lean_ctor_set(x_3061, 1, x_3060);
x_3062 = lean_array_push(x_3032, x_3061);
x_3063 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3064, 0, x_3063);
lean_ctor_set(x_3064, 1, x_3062);
x_3065 = lean_array_push(x_3046, x_3064);
x_3066 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3067, 0, x_3066);
lean_ctor_set(x_3067, 1, x_3065);
x_3068 = 1;
x_3069 = lean_box(x_3068);
if (lean_is_scalar(x_3021)) {
 x_3070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3070 = x_3021;
}
lean_ctor_set(x_3070, 0, x_3067);
lean_ctor_set(x_3070, 1, x_3069);
x_3071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3071, 0, x_3019);
lean_ctor_set(x_3071, 1, x_3070);
if (lean_is_scalar(x_3029)) {
 x_3072 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3072 = x_3029;
}
lean_ctor_set(x_3072, 0, x_3071);
lean_ctor_set(x_3072, 1, x_3028);
return x_3072;
}
}
}
else
{
lean_object* x_3073; lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; lean_object* x_3083; lean_object* x_3084; uint8_t x_3085; 
lean_dec(x_228);
lean_inc(x_5);
x_3073 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_3074 = lean_ctor_get(x_3073, 0);
lean_inc(x_3074);
x_3075 = lean_ctor_get(x_3073, 1);
lean_inc(x_3075);
lean_dec(x_3073);
x_3076 = lean_unsigned_to_nat(1u);
x_3077 = lean_nat_add(x_3, x_3076);
lean_dec(x_3);
x_3078 = l_Lean_mkHole(x_19);
lean_inc(x_3074);
x_3079 = l_Lean_Elab_Term_mkExplicitBinder(x_3074, x_3078);
x_3080 = lean_array_push(x_4, x_3079);
lean_inc(x_5);
x_3081 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3077, x_3080, x_5, x_6, x_7, x_8, x_9, x_10, x_3075);
x_3082 = lean_ctor_get(x_3081, 0);
lean_inc(x_3082);
x_3083 = lean_ctor_get(x_3082, 1);
lean_inc(x_3083);
x_3084 = lean_ctor_get(x_3081, 1);
lean_inc(x_3084);
lean_dec(x_3081);
x_3085 = !lean_is_exclusive(x_3082);
if (x_3085 == 0)
{
lean_object* x_3086; uint8_t x_3087; 
x_3086 = lean_ctor_get(x_3082, 1);
lean_dec(x_3086);
x_3087 = !lean_is_exclusive(x_3083);
if (x_3087 == 0)
{
lean_object* x_3088; lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; uint8_t x_3096; 
x_3088 = lean_ctor_get(x_3083, 0);
x_3089 = lean_ctor_get(x_3083, 1);
lean_dec(x_3089);
x_3090 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_3084);
x_3091 = lean_ctor_get(x_3090, 0);
lean_inc(x_3091);
x_3092 = lean_ctor_get(x_3090, 1);
lean_inc(x_3092);
lean_dec(x_3090);
x_3093 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3092);
lean_dec(x_5);
x_3094 = lean_ctor_get(x_3093, 1);
lean_inc(x_3094);
lean_dec(x_3093);
x_3095 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3094);
x_3096 = !lean_is_exclusive(x_3095);
if (x_3096 == 0)
{
lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; uint8_t x_3119; 
x_3097 = lean_ctor_get(x_3095, 0);
lean_dec(x_3097);
x_3098 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3091);
x_3099 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3099, 0, x_3091);
lean_ctor_set(x_3099, 1, x_3098);
x_3100 = l_Array_empty___closed__1;
x_3101 = lean_array_push(x_3100, x_3099);
x_3102 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3103 = lean_array_push(x_3102, x_3074);
x_3104 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3105, 0, x_3104);
lean_ctor_set(x_3105, 1, x_3103);
x_3106 = lean_array_push(x_3100, x_3105);
x_3107 = l_Lean_nullKind___closed__2;
x_3108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3108, 0, x_3107);
lean_ctor_set(x_3108, 1, x_3106);
x_3109 = lean_array_push(x_3101, x_3108);
x_3110 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3111 = lean_array_push(x_3109, x_3110);
x_3112 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3091);
x_3113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3113, 0, x_3091);
lean_ctor_set(x_3113, 1, x_3112);
x_3114 = lean_array_push(x_3111, x_3113);
x_3115 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3091);
x_3116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3116, 0, x_3091);
lean_ctor_set(x_3116, 1, x_3115);
x_3117 = lean_array_push(x_3100, x_3116);
lean_inc(x_19);
x_3118 = lean_array_push(x_3100, x_19);
x_3119 = !lean_is_exclusive(x_19);
if (x_3119 == 0)
{
lean_object* x_3120; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; lean_object* x_3135; lean_object* x_3136; uint8_t x_3137; lean_object* x_3138; 
x_3120 = lean_ctor_get(x_19, 1);
lean_dec(x_3120);
x_3121 = lean_ctor_get(x_19, 0);
lean_dec(x_3121);
lean_ctor_set(x_19, 1, x_3118);
lean_ctor_set(x_19, 0, x_3107);
x_3122 = lean_array_push(x_3117, x_19);
x_3123 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3124, 0, x_3091);
lean_ctor_set(x_3124, 1, x_3123);
x_3125 = lean_array_push(x_3122, x_3124);
x_3126 = lean_array_push(x_3125, x_3088);
x_3127 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3128, 0, x_3127);
lean_ctor_set(x_3128, 1, x_3126);
x_3129 = lean_array_push(x_3100, x_3128);
x_3130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3130, 0, x_3107);
lean_ctor_set(x_3130, 1, x_3129);
x_3131 = lean_array_push(x_3100, x_3130);
x_3132 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3133, 0, x_3132);
lean_ctor_set(x_3133, 1, x_3131);
x_3134 = lean_array_push(x_3114, x_3133);
x_3135 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3136, 0, x_3135);
lean_ctor_set(x_3136, 1, x_3134);
x_3137 = 1;
x_3138 = lean_box(x_3137);
lean_ctor_set(x_3083, 1, x_3138);
lean_ctor_set(x_3083, 0, x_3136);
lean_ctor_set(x_3095, 0, x_3082);
return x_3095;
}
else
{
lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; uint8_t x_3155; lean_object* x_3156; 
lean_dec(x_19);
x_3139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3139, 0, x_3107);
lean_ctor_set(x_3139, 1, x_3118);
x_3140 = lean_array_push(x_3117, x_3139);
x_3141 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3142, 0, x_3091);
lean_ctor_set(x_3142, 1, x_3141);
x_3143 = lean_array_push(x_3140, x_3142);
x_3144 = lean_array_push(x_3143, x_3088);
x_3145 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3146, 0, x_3145);
lean_ctor_set(x_3146, 1, x_3144);
x_3147 = lean_array_push(x_3100, x_3146);
x_3148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3148, 0, x_3107);
lean_ctor_set(x_3148, 1, x_3147);
x_3149 = lean_array_push(x_3100, x_3148);
x_3150 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3151, 0, x_3150);
lean_ctor_set(x_3151, 1, x_3149);
x_3152 = lean_array_push(x_3114, x_3151);
x_3153 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3154, 0, x_3153);
lean_ctor_set(x_3154, 1, x_3152);
x_3155 = 1;
x_3156 = lean_box(x_3155);
lean_ctor_set(x_3083, 1, x_3156);
lean_ctor_set(x_3083, 0, x_3154);
lean_ctor_set(x_3095, 0, x_3082);
return x_3095;
}
}
else
{
lean_object* x_3157; lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; lean_object* x_3182; lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; lean_object* x_3188; lean_object* x_3189; lean_object* x_3190; lean_object* x_3191; lean_object* x_3192; lean_object* x_3193; lean_object* x_3194; lean_object* x_3195; uint8_t x_3196; lean_object* x_3197; lean_object* x_3198; 
x_3157 = lean_ctor_get(x_3095, 1);
lean_inc(x_3157);
lean_dec(x_3095);
x_3158 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3091);
x_3159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3159, 0, x_3091);
lean_ctor_set(x_3159, 1, x_3158);
x_3160 = l_Array_empty___closed__1;
x_3161 = lean_array_push(x_3160, x_3159);
x_3162 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3163 = lean_array_push(x_3162, x_3074);
x_3164 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3165, 0, x_3164);
lean_ctor_set(x_3165, 1, x_3163);
x_3166 = lean_array_push(x_3160, x_3165);
x_3167 = l_Lean_nullKind___closed__2;
x_3168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3168, 0, x_3167);
lean_ctor_set(x_3168, 1, x_3166);
x_3169 = lean_array_push(x_3161, x_3168);
x_3170 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3171 = lean_array_push(x_3169, x_3170);
x_3172 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3091);
x_3173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3173, 0, x_3091);
lean_ctor_set(x_3173, 1, x_3172);
x_3174 = lean_array_push(x_3171, x_3173);
x_3175 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3091);
x_3176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3176, 0, x_3091);
lean_ctor_set(x_3176, 1, x_3175);
x_3177 = lean_array_push(x_3160, x_3176);
lean_inc(x_19);
x_3178 = lean_array_push(x_3160, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3179 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3179 = lean_box(0);
}
if (lean_is_scalar(x_3179)) {
 x_3180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3180 = x_3179;
}
lean_ctor_set(x_3180, 0, x_3167);
lean_ctor_set(x_3180, 1, x_3178);
x_3181 = lean_array_push(x_3177, x_3180);
x_3182 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3183, 0, x_3091);
lean_ctor_set(x_3183, 1, x_3182);
x_3184 = lean_array_push(x_3181, x_3183);
x_3185 = lean_array_push(x_3184, x_3088);
x_3186 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3187, 0, x_3186);
lean_ctor_set(x_3187, 1, x_3185);
x_3188 = lean_array_push(x_3160, x_3187);
x_3189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3189, 0, x_3167);
lean_ctor_set(x_3189, 1, x_3188);
x_3190 = lean_array_push(x_3160, x_3189);
x_3191 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3192, 0, x_3191);
lean_ctor_set(x_3192, 1, x_3190);
x_3193 = lean_array_push(x_3174, x_3192);
x_3194 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3195, 0, x_3194);
lean_ctor_set(x_3195, 1, x_3193);
x_3196 = 1;
x_3197 = lean_box(x_3196);
lean_ctor_set(x_3083, 1, x_3197);
lean_ctor_set(x_3083, 0, x_3195);
x_3198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3198, 0, x_3082);
lean_ctor_set(x_3198, 1, x_3157);
return x_3198;
}
}
else
{
lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; lean_object* x_3229; lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; lean_object* x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; uint8_t x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; 
x_3199 = lean_ctor_get(x_3083, 0);
lean_inc(x_3199);
lean_dec(x_3083);
x_3200 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_3084);
x_3201 = lean_ctor_get(x_3200, 0);
lean_inc(x_3201);
x_3202 = lean_ctor_get(x_3200, 1);
lean_inc(x_3202);
lean_dec(x_3200);
x_3203 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3202);
lean_dec(x_5);
x_3204 = lean_ctor_get(x_3203, 1);
lean_inc(x_3204);
lean_dec(x_3203);
x_3205 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3204);
x_3206 = lean_ctor_get(x_3205, 1);
lean_inc(x_3206);
if (lean_is_exclusive(x_3205)) {
 lean_ctor_release(x_3205, 0);
 lean_ctor_release(x_3205, 1);
 x_3207 = x_3205;
} else {
 lean_dec_ref(x_3205);
 x_3207 = lean_box(0);
}
x_3208 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3201);
x_3209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3209, 0, x_3201);
lean_ctor_set(x_3209, 1, x_3208);
x_3210 = l_Array_empty___closed__1;
x_3211 = lean_array_push(x_3210, x_3209);
x_3212 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3213 = lean_array_push(x_3212, x_3074);
x_3214 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3215, 0, x_3214);
lean_ctor_set(x_3215, 1, x_3213);
x_3216 = lean_array_push(x_3210, x_3215);
x_3217 = l_Lean_nullKind___closed__2;
x_3218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3218, 0, x_3217);
lean_ctor_set(x_3218, 1, x_3216);
x_3219 = lean_array_push(x_3211, x_3218);
x_3220 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3221 = lean_array_push(x_3219, x_3220);
x_3222 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3201);
x_3223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3223, 0, x_3201);
lean_ctor_set(x_3223, 1, x_3222);
x_3224 = lean_array_push(x_3221, x_3223);
x_3225 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3201);
x_3226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3226, 0, x_3201);
lean_ctor_set(x_3226, 1, x_3225);
x_3227 = lean_array_push(x_3210, x_3226);
lean_inc(x_19);
x_3228 = lean_array_push(x_3210, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3229 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3229 = lean_box(0);
}
if (lean_is_scalar(x_3229)) {
 x_3230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3230 = x_3229;
}
lean_ctor_set(x_3230, 0, x_3217);
lean_ctor_set(x_3230, 1, x_3228);
x_3231 = lean_array_push(x_3227, x_3230);
x_3232 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3233, 0, x_3201);
lean_ctor_set(x_3233, 1, x_3232);
x_3234 = lean_array_push(x_3231, x_3233);
x_3235 = lean_array_push(x_3234, x_3199);
x_3236 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3237, 0, x_3236);
lean_ctor_set(x_3237, 1, x_3235);
x_3238 = lean_array_push(x_3210, x_3237);
x_3239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3239, 0, x_3217);
lean_ctor_set(x_3239, 1, x_3238);
x_3240 = lean_array_push(x_3210, x_3239);
x_3241 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3242, 0, x_3241);
lean_ctor_set(x_3242, 1, x_3240);
x_3243 = lean_array_push(x_3224, x_3242);
x_3244 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3245, 0, x_3244);
lean_ctor_set(x_3245, 1, x_3243);
x_3246 = 1;
x_3247 = lean_box(x_3246);
x_3248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3248, 0, x_3245);
lean_ctor_set(x_3248, 1, x_3247);
lean_ctor_set(x_3082, 1, x_3248);
if (lean_is_scalar(x_3207)) {
 x_3249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3249 = x_3207;
}
lean_ctor_set(x_3249, 0, x_3082);
lean_ctor_set(x_3249, 1, x_3206);
return x_3249;
}
}
else
{
lean_object* x_3250; lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; lean_object* x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; uint8_t x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; 
x_3250 = lean_ctor_get(x_3082, 0);
lean_inc(x_3250);
lean_dec(x_3082);
x_3251 = lean_ctor_get(x_3083, 0);
lean_inc(x_3251);
if (lean_is_exclusive(x_3083)) {
 lean_ctor_release(x_3083, 0);
 lean_ctor_release(x_3083, 1);
 x_3252 = x_3083;
} else {
 lean_dec_ref(x_3083);
 x_3252 = lean_box(0);
}
x_3253 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_3084);
x_3254 = lean_ctor_get(x_3253, 0);
lean_inc(x_3254);
x_3255 = lean_ctor_get(x_3253, 1);
lean_inc(x_3255);
lean_dec(x_3253);
x_3256 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3255);
lean_dec(x_5);
x_3257 = lean_ctor_get(x_3256, 1);
lean_inc(x_3257);
lean_dec(x_3256);
x_3258 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3257);
x_3259 = lean_ctor_get(x_3258, 1);
lean_inc(x_3259);
if (lean_is_exclusive(x_3258)) {
 lean_ctor_release(x_3258, 0);
 lean_ctor_release(x_3258, 1);
 x_3260 = x_3258;
} else {
 lean_dec_ref(x_3258);
 x_3260 = lean_box(0);
}
x_3261 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3254);
x_3262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3262, 0, x_3254);
lean_ctor_set(x_3262, 1, x_3261);
x_3263 = l_Array_empty___closed__1;
x_3264 = lean_array_push(x_3263, x_3262);
x_3265 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3266 = lean_array_push(x_3265, x_3074);
x_3267 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3268, 0, x_3267);
lean_ctor_set(x_3268, 1, x_3266);
x_3269 = lean_array_push(x_3263, x_3268);
x_3270 = l_Lean_nullKind___closed__2;
x_3271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3271, 0, x_3270);
lean_ctor_set(x_3271, 1, x_3269);
x_3272 = lean_array_push(x_3264, x_3271);
x_3273 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3274 = lean_array_push(x_3272, x_3273);
x_3275 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3254);
x_3276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3276, 0, x_3254);
lean_ctor_set(x_3276, 1, x_3275);
x_3277 = lean_array_push(x_3274, x_3276);
x_3278 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3254);
x_3279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3279, 0, x_3254);
lean_ctor_set(x_3279, 1, x_3278);
x_3280 = lean_array_push(x_3263, x_3279);
lean_inc(x_19);
x_3281 = lean_array_push(x_3263, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3282 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3282 = lean_box(0);
}
if (lean_is_scalar(x_3282)) {
 x_3283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3283 = x_3282;
}
lean_ctor_set(x_3283, 0, x_3270);
lean_ctor_set(x_3283, 1, x_3281);
x_3284 = lean_array_push(x_3280, x_3283);
x_3285 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3286 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3286, 0, x_3254);
lean_ctor_set(x_3286, 1, x_3285);
x_3287 = lean_array_push(x_3284, x_3286);
x_3288 = lean_array_push(x_3287, x_3251);
x_3289 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3290, 0, x_3289);
lean_ctor_set(x_3290, 1, x_3288);
x_3291 = lean_array_push(x_3263, x_3290);
x_3292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3292, 0, x_3270);
lean_ctor_set(x_3292, 1, x_3291);
x_3293 = lean_array_push(x_3263, x_3292);
x_3294 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3295, 0, x_3294);
lean_ctor_set(x_3295, 1, x_3293);
x_3296 = lean_array_push(x_3277, x_3295);
x_3297 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3298, 0, x_3297);
lean_ctor_set(x_3298, 1, x_3296);
x_3299 = 1;
x_3300 = lean_box(x_3299);
if (lean_is_scalar(x_3252)) {
 x_3301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3301 = x_3252;
}
lean_ctor_set(x_3301, 0, x_3298);
lean_ctor_set(x_3301, 1, x_3300);
x_3302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3302, 0, x_3250);
lean_ctor_set(x_3302, 1, x_3301);
if (lean_is_scalar(x_3260)) {
 x_3303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3303 = x_3260;
}
lean_ctor_set(x_3303, 0, x_3302);
lean_ctor_set(x_3303, 1, x_3259);
return x_3303;
}
}
}
case 2:
{
lean_object* x_3304; lean_object* x_3305; lean_object* x_3306; lean_object* x_3307; lean_object* x_3308; lean_object* x_3309; lean_object* x_3310; lean_object* x_3311; lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; lean_object* x_3315; uint8_t x_3316; 
lean_inc(x_5);
x_3304 = l_Lean_Elab_Term_mkFreshIdent(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_3305 = lean_ctor_get(x_3304, 0);
lean_inc(x_3305);
x_3306 = lean_ctor_get(x_3304, 1);
lean_inc(x_3306);
lean_dec(x_3304);
x_3307 = lean_unsigned_to_nat(1u);
x_3308 = lean_nat_add(x_3, x_3307);
lean_dec(x_3);
x_3309 = l_Lean_mkHole(x_19);
lean_inc(x_3305);
x_3310 = l_Lean_Elab_Term_mkExplicitBinder(x_3305, x_3309);
x_3311 = lean_array_push(x_4, x_3310);
lean_inc(x_5);
x_3312 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3308, x_3311, x_5, x_6, x_7, x_8, x_9, x_10, x_3306);
x_3313 = lean_ctor_get(x_3312, 0);
lean_inc(x_3313);
x_3314 = lean_ctor_get(x_3313, 1);
lean_inc(x_3314);
x_3315 = lean_ctor_get(x_3312, 1);
lean_inc(x_3315);
lean_dec(x_3312);
x_3316 = !lean_is_exclusive(x_3313);
if (x_3316 == 0)
{
lean_object* x_3317; uint8_t x_3318; 
x_3317 = lean_ctor_get(x_3313, 1);
lean_dec(x_3317);
x_3318 = !lean_is_exclusive(x_3314);
if (x_3318 == 0)
{
lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; uint8_t x_3327; 
x_3319 = lean_ctor_get(x_3314, 0);
x_3320 = lean_ctor_get(x_3314, 1);
lean_dec(x_3320);
x_3321 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_3315);
x_3322 = lean_ctor_get(x_3321, 0);
lean_inc(x_3322);
x_3323 = lean_ctor_get(x_3321, 1);
lean_inc(x_3323);
lean_dec(x_3321);
x_3324 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3323);
lean_dec(x_5);
x_3325 = lean_ctor_get(x_3324, 1);
lean_inc(x_3325);
lean_dec(x_3324);
x_3326 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3325);
x_3327 = !lean_is_exclusive(x_3326);
if (x_3327 == 0)
{
lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; lean_object* x_3349; uint8_t x_3350; 
x_3328 = lean_ctor_get(x_3326, 0);
lean_dec(x_3328);
x_3329 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3322);
x_3330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3330, 0, x_3322);
lean_ctor_set(x_3330, 1, x_3329);
x_3331 = l_Array_empty___closed__1;
x_3332 = lean_array_push(x_3331, x_3330);
x_3333 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3334 = lean_array_push(x_3333, x_3305);
x_3335 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3336, 0, x_3335);
lean_ctor_set(x_3336, 1, x_3334);
x_3337 = lean_array_push(x_3331, x_3336);
x_3338 = l_Lean_nullKind___closed__2;
x_3339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3339, 0, x_3338);
lean_ctor_set(x_3339, 1, x_3337);
x_3340 = lean_array_push(x_3332, x_3339);
x_3341 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3342 = lean_array_push(x_3340, x_3341);
x_3343 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3322);
x_3344 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3344, 0, x_3322);
lean_ctor_set(x_3344, 1, x_3343);
x_3345 = lean_array_push(x_3342, x_3344);
x_3346 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3322);
x_3347 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3347, 0, x_3322);
lean_ctor_set(x_3347, 1, x_3346);
x_3348 = lean_array_push(x_3331, x_3347);
lean_inc(x_19);
x_3349 = lean_array_push(x_3331, x_19);
x_3350 = !lean_is_exclusive(x_19);
if (x_3350 == 0)
{
lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; lean_object* x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; lean_object* x_3366; lean_object* x_3367; uint8_t x_3368; lean_object* x_3369; 
x_3351 = lean_ctor_get(x_19, 1);
lean_dec(x_3351);
x_3352 = lean_ctor_get(x_19, 0);
lean_dec(x_3352);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_3349);
lean_ctor_set(x_19, 0, x_3338);
x_3353 = lean_array_push(x_3348, x_19);
x_3354 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3355, 0, x_3322);
lean_ctor_set(x_3355, 1, x_3354);
x_3356 = lean_array_push(x_3353, x_3355);
x_3357 = lean_array_push(x_3356, x_3319);
x_3358 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3359, 0, x_3358);
lean_ctor_set(x_3359, 1, x_3357);
x_3360 = lean_array_push(x_3331, x_3359);
x_3361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3361, 0, x_3338);
lean_ctor_set(x_3361, 1, x_3360);
x_3362 = lean_array_push(x_3331, x_3361);
x_3363 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3364, 0, x_3363);
lean_ctor_set(x_3364, 1, x_3362);
x_3365 = lean_array_push(x_3345, x_3364);
x_3366 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3367, 0, x_3366);
lean_ctor_set(x_3367, 1, x_3365);
x_3368 = 1;
x_3369 = lean_box(x_3368);
lean_ctor_set(x_3314, 1, x_3369);
lean_ctor_set(x_3314, 0, x_3367);
lean_ctor_set(x_3326, 0, x_3313);
return x_3326;
}
else
{
lean_object* x_3370; lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; lean_object* x_3375; lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; lean_object* x_3385; uint8_t x_3386; lean_object* x_3387; 
lean_dec(x_19);
x_3370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3370, 0, x_3338);
lean_ctor_set(x_3370, 1, x_3349);
x_3371 = lean_array_push(x_3348, x_3370);
x_3372 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3373, 0, x_3322);
lean_ctor_set(x_3373, 1, x_3372);
x_3374 = lean_array_push(x_3371, x_3373);
x_3375 = lean_array_push(x_3374, x_3319);
x_3376 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3377, 0, x_3376);
lean_ctor_set(x_3377, 1, x_3375);
x_3378 = lean_array_push(x_3331, x_3377);
x_3379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3379, 0, x_3338);
lean_ctor_set(x_3379, 1, x_3378);
x_3380 = lean_array_push(x_3331, x_3379);
x_3381 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3382, 0, x_3381);
lean_ctor_set(x_3382, 1, x_3380);
x_3383 = lean_array_push(x_3345, x_3382);
x_3384 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3385, 0, x_3384);
lean_ctor_set(x_3385, 1, x_3383);
x_3386 = 1;
x_3387 = lean_box(x_3386);
lean_ctor_set(x_3314, 1, x_3387);
lean_ctor_set(x_3314, 0, x_3385);
lean_ctor_set(x_3326, 0, x_3313);
return x_3326;
}
}
else
{
lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; uint8_t x_3427; lean_object* x_3428; lean_object* x_3429; 
x_3388 = lean_ctor_get(x_3326, 1);
lean_inc(x_3388);
lean_dec(x_3326);
x_3389 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3322);
x_3390 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3390, 0, x_3322);
lean_ctor_set(x_3390, 1, x_3389);
x_3391 = l_Array_empty___closed__1;
x_3392 = lean_array_push(x_3391, x_3390);
x_3393 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3394 = lean_array_push(x_3393, x_3305);
x_3395 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3396, 0, x_3395);
lean_ctor_set(x_3396, 1, x_3394);
x_3397 = lean_array_push(x_3391, x_3396);
x_3398 = l_Lean_nullKind___closed__2;
x_3399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3399, 0, x_3398);
lean_ctor_set(x_3399, 1, x_3397);
x_3400 = lean_array_push(x_3392, x_3399);
x_3401 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3402 = lean_array_push(x_3400, x_3401);
x_3403 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3322);
x_3404 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3404, 0, x_3322);
lean_ctor_set(x_3404, 1, x_3403);
x_3405 = lean_array_push(x_3402, x_3404);
x_3406 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3322);
x_3407 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3407, 0, x_3322);
lean_ctor_set(x_3407, 1, x_3406);
x_3408 = lean_array_push(x_3391, x_3407);
lean_inc(x_19);
x_3409 = lean_array_push(x_3391, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3410 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3410 = lean_box(0);
}
if (lean_is_scalar(x_3410)) {
 x_3411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3411 = x_3410;
 lean_ctor_set_tag(x_3411, 1);
}
lean_ctor_set(x_3411, 0, x_3398);
lean_ctor_set(x_3411, 1, x_3409);
x_3412 = lean_array_push(x_3408, x_3411);
x_3413 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3414 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3414, 0, x_3322);
lean_ctor_set(x_3414, 1, x_3413);
x_3415 = lean_array_push(x_3412, x_3414);
x_3416 = lean_array_push(x_3415, x_3319);
x_3417 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3418, 0, x_3417);
lean_ctor_set(x_3418, 1, x_3416);
x_3419 = lean_array_push(x_3391, x_3418);
x_3420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3420, 0, x_3398);
lean_ctor_set(x_3420, 1, x_3419);
x_3421 = lean_array_push(x_3391, x_3420);
x_3422 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3423, 0, x_3422);
lean_ctor_set(x_3423, 1, x_3421);
x_3424 = lean_array_push(x_3405, x_3423);
x_3425 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3426, 0, x_3425);
lean_ctor_set(x_3426, 1, x_3424);
x_3427 = 1;
x_3428 = lean_box(x_3427);
lean_ctor_set(x_3314, 1, x_3428);
lean_ctor_set(x_3314, 0, x_3426);
x_3429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3429, 0, x_3313);
lean_ctor_set(x_3429, 1, x_3388);
return x_3429;
}
}
else
{
lean_object* x_3430; lean_object* x_3431; lean_object* x_3432; lean_object* x_3433; lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; lean_object* x_3438; lean_object* x_3439; lean_object* x_3440; lean_object* x_3441; lean_object* x_3442; lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; lean_object* x_3448; lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; lean_object* x_3454; lean_object* x_3455; lean_object* x_3456; lean_object* x_3457; lean_object* x_3458; lean_object* x_3459; lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; lean_object* x_3470; lean_object* x_3471; lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; uint8_t x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; 
x_3430 = lean_ctor_get(x_3314, 0);
lean_inc(x_3430);
lean_dec(x_3314);
x_3431 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_3315);
x_3432 = lean_ctor_get(x_3431, 0);
lean_inc(x_3432);
x_3433 = lean_ctor_get(x_3431, 1);
lean_inc(x_3433);
lean_dec(x_3431);
x_3434 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3433);
lean_dec(x_5);
x_3435 = lean_ctor_get(x_3434, 1);
lean_inc(x_3435);
lean_dec(x_3434);
x_3436 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3435);
x_3437 = lean_ctor_get(x_3436, 1);
lean_inc(x_3437);
if (lean_is_exclusive(x_3436)) {
 lean_ctor_release(x_3436, 0);
 lean_ctor_release(x_3436, 1);
 x_3438 = x_3436;
} else {
 lean_dec_ref(x_3436);
 x_3438 = lean_box(0);
}
x_3439 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3432);
x_3440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3440, 0, x_3432);
lean_ctor_set(x_3440, 1, x_3439);
x_3441 = l_Array_empty___closed__1;
x_3442 = lean_array_push(x_3441, x_3440);
x_3443 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3444 = lean_array_push(x_3443, x_3305);
x_3445 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3446, 0, x_3445);
lean_ctor_set(x_3446, 1, x_3444);
x_3447 = lean_array_push(x_3441, x_3446);
x_3448 = l_Lean_nullKind___closed__2;
x_3449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3449, 0, x_3448);
lean_ctor_set(x_3449, 1, x_3447);
x_3450 = lean_array_push(x_3442, x_3449);
x_3451 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3452 = lean_array_push(x_3450, x_3451);
x_3453 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3432);
x_3454 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3454, 0, x_3432);
lean_ctor_set(x_3454, 1, x_3453);
x_3455 = lean_array_push(x_3452, x_3454);
x_3456 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3432);
x_3457 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3457, 0, x_3432);
lean_ctor_set(x_3457, 1, x_3456);
x_3458 = lean_array_push(x_3441, x_3457);
lean_inc(x_19);
x_3459 = lean_array_push(x_3441, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3460 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3460 = lean_box(0);
}
if (lean_is_scalar(x_3460)) {
 x_3461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3461 = x_3460;
 lean_ctor_set_tag(x_3461, 1);
}
lean_ctor_set(x_3461, 0, x_3448);
lean_ctor_set(x_3461, 1, x_3459);
x_3462 = lean_array_push(x_3458, x_3461);
x_3463 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3464 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3464, 0, x_3432);
lean_ctor_set(x_3464, 1, x_3463);
x_3465 = lean_array_push(x_3462, x_3464);
x_3466 = lean_array_push(x_3465, x_3430);
x_3467 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3468, 0, x_3467);
lean_ctor_set(x_3468, 1, x_3466);
x_3469 = lean_array_push(x_3441, x_3468);
x_3470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3470, 0, x_3448);
lean_ctor_set(x_3470, 1, x_3469);
x_3471 = lean_array_push(x_3441, x_3470);
x_3472 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3473, 0, x_3472);
lean_ctor_set(x_3473, 1, x_3471);
x_3474 = lean_array_push(x_3455, x_3473);
x_3475 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3476, 0, x_3475);
lean_ctor_set(x_3476, 1, x_3474);
x_3477 = 1;
x_3478 = lean_box(x_3477);
x_3479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3479, 0, x_3476);
lean_ctor_set(x_3479, 1, x_3478);
lean_ctor_set(x_3313, 1, x_3479);
if (lean_is_scalar(x_3438)) {
 x_3480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3480 = x_3438;
}
lean_ctor_set(x_3480, 0, x_3313);
lean_ctor_set(x_3480, 1, x_3437);
return x_3480;
}
}
else
{
lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3499; lean_object* x_3500; lean_object* x_3501; lean_object* x_3502; lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; lean_object* x_3507; lean_object* x_3508; lean_object* x_3509; lean_object* x_3510; lean_object* x_3511; lean_object* x_3512; lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; uint8_t x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; 
x_3481 = lean_ctor_get(x_3313, 0);
lean_inc(x_3481);
lean_dec(x_3313);
x_3482 = lean_ctor_get(x_3314, 0);
lean_inc(x_3482);
if (lean_is_exclusive(x_3314)) {
 lean_ctor_release(x_3314, 0);
 lean_ctor_release(x_3314, 1);
 x_3483 = x_3314;
} else {
 lean_dec_ref(x_3314);
 x_3483 = lean_box(0);
}
x_3484 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_3315);
x_3485 = lean_ctor_get(x_3484, 0);
lean_inc(x_3485);
x_3486 = lean_ctor_get(x_3484, 1);
lean_inc(x_3486);
lean_dec(x_3484);
x_3487 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_3486);
lean_dec(x_5);
x_3488 = lean_ctor_get(x_3487, 1);
lean_inc(x_3488);
lean_dec(x_3487);
x_3489 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_3488);
x_3490 = lean_ctor_get(x_3489, 1);
lean_inc(x_3490);
if (lean_is_exclusive(x_3489)) {
 lean_ctor_release(x_3489, 0);
 lean_ctor_release(x_3489, 1);
 x_3491 = x_3489;
} else {
 lean_dec_ref(x_3489);
 x_3491 = lean_box(0);
}
x_3492 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_3485);
x_3493 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3493, 0, x_3485);
lean_ctor_set(x_3493, 1, x_3492);
x_3494 = l_Array_empty___closed__1;
x_3495 = lean_array_push(x_3494, x_3493);
x_3496 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_3497 = lean_array_push(x_3496, x_3305);
x_3498 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_3499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3499, 0, x_3498);
lean_ctor_set(x_3499, 1, x_3497);
x_3500 = lean_array_push(x_3494, x_3499);
x_3501 = l_Lean_nullKind___closed__2;
x_3502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3502, 0, x_3501);
lean_ctor_set(x_3502, 1, x_3500);
x_3503 = lean_array_push(x_3495, x_3502);
x_3504 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_3505 = lean_array_push(x_3503, x_3504);
x_3506 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_3485);
x_3507 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3507, 0, x_3485);
lean_ctor_set(x_3507, 1, x_3506);
x_3508 = lean_array_push(x_3505, x_3507);
x_3509 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_3485);
x_3510 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3510, 0, x_3485);
lean_ctor_set(x_3510, 1, x_3509);
x_3511 = lean_array_push(x_3494, x_3510);
lean_inc(x_19);
x_3512 = lean_array_push(x_3494, x_19);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_3513 = x_19;
} else {
 lean_dec_ref(x_19);
 x_3513 = lean_box(0);
}
if (lean_is_scalar(x_3513)) {
 x_3514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3514 = x_3513;
 lean_ctor_set_tag(x_3514, 1);
}
lean_ctor_set(x_3514, 0, x_3501);
lean_ctor_set(x_3514, 1, x_3512);
x_3515 = lean_array_push(x_3511, x_3514);
x_3516 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_3517 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3517, 0, x_3485);
lean_ctor_set(x_3517, 1, x_3516);
x_3518 = lean_array_push(x_3515, x_3517);
x_3519 = lean_array_push(x_3518, x_3482);
x_3520 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_3521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3521, 0, x_3520);
lean_ctor_set(x_3521, 1, x_3519);
x_3522 = lean_array_push(x_3494, x_3521);
x_3523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3523, 0, x_3501);
lean_ctor_set(x_3523, 1, x_3522);
x_3524 = lean_array_push(x_3494, x_3523);
x_3525 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_3526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3526, 0, x_3525);
lean_ctor_set(x_3526, 1, x_3524);
x_3527 = lean_array_push(x_3508, x_3526);
x_3528 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_3529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3529, 0, x_3528);
lean_ctor_set(x_3529, 1, x_3527);
x_3530 = 1;
x_3531 = lean_box(x_3530);
if (lean_is_scalar(x_3483)) {
 x_3532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3532 = x_3483;
}
lean_ctor_set(x_3532, 0, x_3529);
lean_ctor_set(x_3532, 1, x_3531);
x_3533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3533, 0, x_3481);
lean_ctor_set(x_3533, 1, x_3532);
if (lean_is_scalar(x_3491)) {
 x_3534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3534 = x_3491;
}
lean_ctor_set(x_3534, 0, x_3533);
lean_ctor_set(x_3534, 1, x_3490);
return x_3534;
}
}
default: 
{
lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; 
x_3535 = l_Lean_mkHole(x_19);
x_3536 = lean_unsigned_to_nat(1u);
x_3537 = lean_nat_add(x_3, x_3536);
lean_dec(x_3);
x_3538 = l_Lean_Elab_Term_mkExplicitBinder(x_19, x_3535);
x_3539 = lean_array_push(x_4, x_3538);
x_3 = x_3537;
x_4 = x_3539;
goto _start;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_expandFunBinders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
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
lean_dec(x_14);
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
x_3 = l_Lean_nullKind___closed__2;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Syntax_getArgs(x_2);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = l_Lean_Parser_Term_letRecDecl___elambda__1___closed__1;
x_14 = lean_name_mk_string(x_1, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
lean_dec(x_2);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_18);
x_20 = l_Lean_Syntax_isOfKind(x_18, x_3);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_12);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_23, x_17);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_12);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_12);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_12);
return x_27;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadEST___closed__1;
x_2 = l_Lean_instInhabitedSyntax;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.expandWhereDecls");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__1;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__3;
x_3 = lean_unsigned_to_nat(384u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_expandWhereDecls___closed__2;
x_8 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_9 = lean_panic_fn(x_7, x_8);
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
x_15 = l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_5198____spec__1(x_13, x_14);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = l_Lean_Elab_Term_expandWhereDecls___closed__2;
x_17 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_18 = lean_panic_fn(x_16, x_17);
x_19 = lean_apply_2(x_18, x_3, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_3, x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_myMacro____x40_Init_Notation___hyg_16009____closed__1;
lean_inc(x_23);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__3;
lean_inc(x_23);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_27, x_29);
x_31 = l_Lean_nullKind___closed__2;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_array_push(x_26, x_32);
x_34 = l_myMacro____x40_Init_Notation___hyg_1272____closed__7;
x_35 = l_Lean_Syntax_SepArray_ofElems(x_34, x_20);
lean_dec(x_20);
x_36 = l_Array_appendCore___rarg(x_26, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_push(x_26, x_37);
x_39 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__1;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_33, x_40);
x_42 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_26, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_41, x_45);
x_47 = lean_array_push(x_46, x_2);
x_48 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_21, 0, x_49);
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = l_myMacro____x40_Init_Notation___hyg_16009____closed__1;
lean_inc(x_50);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__3;
lean_inc(x_50);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_55, x_57);
x_59 = l_Lean_nullKind___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_54, x_60);
x_62 = l_myMacro____x40_Init_Notation___hyg_1272____closed__7;
x_63 = l_Lean_Syntax_SepArray_ofElems(x_62, x_20);
lean_dec(x_20);
x_64 = l_Array_appendCore___rarg(x_54, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_54, x_65);
x_67 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__1;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_61, x_68);
x_70 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_50);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_54, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_69, x_73);
x_75 = lean_array_push(x_74, x_2);
x_76 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20507____closed__2;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_51);
return x_78;
}
}
}
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
lean_dec(x_3);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = l_myMacro____x40_Init_Notation___hyg_14520____closed__3;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
lean_inc(x_2);
lean_inc(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_2);
lean_inc(x_2);
x_16 = lean_array_push(x_2, x_15);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = 1;
x_20 = x_5 + x_19;
x_21 = x_18;
x_22 = lean_array_uset(x_11, x_5, x_21);
x_5 = x_20;
x_6 = x_22;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
x_15 = l_myMacro____x40_Init_Notation___hyg_14520____closed__3;
x_16 = lean_name_mk_string(x_14, x_15);
lean_inc(x_2);
lean_inc(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_2);
lean_inc(x_2);
x_18 = lean_array_push(x_2, x_17);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = x_5 + x_21;
x_23 = x_20;
x_24 = lean_array_uset(x_11, x_5, x_23);
x_5 = x_22;
x_6 = x_24;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
x_11 = lean_nat_add(x_6, x_9);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_13);
lean_ctor_set(x_5, 2, x_6);
x_15 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(x_5, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkArrow___closed__2;
x_19 = l_Lean_addMacroScope(x_13, x_18, x_6);
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_inc(x_22);
x_23 = lean_array_push(x_4, x_22);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_23, x_5, x_17);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_26);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_29);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Array_empty___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_29);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_push(x_32, x_35);
x_37 = lean_array_push(x_32, x_22);
x_38 = l_Lean_nullKind___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_32, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_40, x_42);
x_44 = lean_array_push(x_43, x_25);
x_45 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_36, x_46);
x_48 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_33, x_49);
x_51 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_27, 0, x_52);
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
x_55 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_53);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_empty___closed__1;
x_58 = lean_array_push(x_57, x_56);
x_59 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_53);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_push(x_57, x_60);
x_62 = lean_array_push(x_57, x_22);
x_63 = l_Lean_nullKind___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_57, x_64);
x_66 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_65, x_67);
x_69 = lean_array_push(x_68, x_25);
x_70 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_push(x_61, x_71);
x_73 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_array_push(x_58, x_74);
x_76 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_54);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_24, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_24, 1);
lean_inc(x_80);
lean_dec(x_24);
x_81 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_80);
lean_dec(x_5);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_83);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Array_empty___closed__1;
x_87 = lean_array_push(x_86, x_85);
x_88 = lean_array_push(x_86, x_22);
x_89 = l_Lean_nullKind___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_87, x_90);
x_92 = l_Lean_Parser_Tactic_intro___closed__4;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_86, x_93);
x_95 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_94, x_96);
x_98 = lean_array_push(x_97, x_79);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_push(x_86, x_99);
x_101 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17279____closed__2;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_81, 0, x_102);
return x_81;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_103 = lean_ctor_get(x_81, 0);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_81);
x_105 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_103);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Array_empty___closed__1;
x_108 = lean_array_push(x_107, x_106);
x_109 = lean_array_push(x_107, x_22);
x_110 = l_Lean_nullKind___closed__2;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_array_push(x_108, x_111);
x_113 = l_Lean_Parser_Tactic_intro___closed__4;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_array_push(x_107, x_114);
x_116 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_array_push(x_115, x_117);
x_119 = lean_array_push(x_118, x_79);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_107, x_120);
x_122 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17279____closed__2;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_104);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_125 = lean_ctor_get(x_5, 0);
x_126 = lean_ctor_get(x_5, 1);
x_127 = lean_ctor_get(x_5, 3);
x_128 = lean_ctor_get(x_5, 4);
x_129 = lean_ctor_get(x_5, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_126);
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_130, 2, x_6);
lean_ctor_set(x_130, 3, x_127);
lean_ctor_set(x_130, 4, x_128);
lean_ctor_set(x_130, 5, x_129);
x_131 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(x_130, x_11);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Meta_mkArrow___closed__2;
x_135 = l_Lean_addMacroScope(x_126, x_134, x_6);
x_136 = lean_box(0);
x_137 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_138 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_135);
lean_ctor_set(x_138, 3, x_136);
lean_inc(x_138);
x_139 = lean_array_push(x_4, x_138);
lean_inc(x_130);
x_140 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_139, x_130, x_133);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_130, x_142);
lean_dec(x_130);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_144);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Array_empty___closed__1;
x_150 = lean_array_push(x_149, x_148);
x_151 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_144);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_push(x_149, x_152);
x_154 = lean_array_push(x_149, x_138);
x_155 = l_Lean_nullKind___closed__2;
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_array_push(x_149, x_156);
x_158 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_144);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_array_push(x_157, x_159);
x_161 = lean_array_push(x_160, x_141);
x_162 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_array_push(x_153, x_163);
x_165 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_array_push(x_150, x_166);
x_168 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
if (lean_is_scalar(x_146)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_146;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_145);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_171 = lean_ctor_get(x_140, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_140, 1);
lean_inc(x_172);
lean_dec(x_140);
x_173 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_130, x_172);
lean_dec(x_130);
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
x_177 = l_Lean_Parser_Tactic_intro___closed__3;
lean_inc(x_174);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Array_empty___closed__1;
x_180 = lean_array_push(x_179, x_178);
x_181 = lean_array_push(x_179, x_138);
x_182 = l_Lean_nullKind___closed__2;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_array_push(x_180, x_183);
x_185 = l_Lean_Parser_Tactic_intro___closed__4;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_array_push(x_179, x_186);
x_188 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_174);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_187, x_189);
x_191 = lean_array_push(x_190, x_171);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_array_push(x_179, x_192);
x_194 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17279____closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
if (lean_is_scalar(x_176)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_176;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_175);
return x_196;
}
}
}
else
{
if (x_2 == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
lean_dec(x_5);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; size_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_199);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Array_empty___closed__1;
x_203 = lean_array_push(x_202, x_201);
x_204 = lean_array_get_size(x_4);
x_205 = lean_usize_of_nat(x_204);
lean_dec(x_204);
x_206 = 0;
x_207 = x_4;
x_208 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_209 = l_Lean_nullKind___closed__2;
x_210 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_208, x_202, x_209, x_205, x_206, x_207);
x_211 = x_210;
x_212 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_213 = l_Lean_mkSepArray(x_211, x_212);
lean_dec(x_211);
x_214 = l_Array_appendCore___rarg(x_202, x_213);
lean_dec(x_213);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_209);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_array_push(x_203, x_215);
x_217 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_218 = lean_array_push(x_216, x_217);
x_219 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_199);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_array_push(x_218, x_220);
x_222 = lean_array_push(x_221, x_1);
x_223 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
lean_ctor_set(x_197, 0, x_224);
return x_197;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; size_t x_232; size_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_225 = lean_ctor_get(x_197, 0);
x_226 = lean_ctor_get(x_197, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_197);
x_227 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_225);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Array_empty___closed__1;
x_230 = lean_array_push(x_229, x_228);
x_231 = lean_array_get_size(x_4);
x_232 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_233 = 0;
x_234 = x_4;
x_235 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_236 = l_Lean_nullKind___closed__2;
x_237 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_235, x_229, x_236, x_232, x_233, x_234);
x_238 = x_237;
x_239 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_240 = l_Lean_mkSepArray(x_238, x_239);
lean_dec(x_238);
x_241 = l_Array_appendCore___rarg(x_229, x_240);
lean_dec(x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_array_push(x_230, x_242);
x_244 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_245 = lean_array_push(x_243, x_244);
x_246 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_225);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_array_push(x_245, x_247);
x_249 = lean_array_push(x_248, x_1);
x_250 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_226);
return x_252;
}
}
else
{
lean_object* x_253; uint8_t x_254; 
x_253 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_6);
lean_dec(x_5);
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; size_t x_261; size_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_255 = lean_ctor_get(x_253, 0);
x_256 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_255);
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Array_empty___closed__1;
x_259 = lean_array_push(x_258, x_257);
x_260 = lean_array_get_size(x_4);
x_261 = lean_usize_of_nat(x_260);
lean_dec(x_260);
x_262 = 0;
x_263 = x_4;
x_264 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_265 = l_Lean_nullKind___closed__2;
x_266 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_264, x_258, x_265, x_261, x_262, x_263);
x_267 = x_266;
x_268 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_269 = l_Lean_mkSepArray(x_267, x_268);
lean_dec(x_267);
x_270 = l_Array_appendCore___rarg(x_258, x_269);
lean_dec(x_269);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_265);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_array_push(x_259, x_271);
x_273 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_274 = lean_array_push(x_272, x_273);
x_275 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_255);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_array_push(x_274, x_276);
x_278 = lean_array_push(x_277, x_1);
x_279 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
lean_ctor_set(x_253, 0, x_280);
return x_253;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; size_t x_288; size_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_281 = lean_ctor_get(x_253, 0);
x_282 = lean_ctor_get(x_253, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_253);
x_283 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_281);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Array_empty___closed__1;
x_286 = lean_array_push(x_285, x_284);
x_287 = lean_array_get_size(x_4);
x_288 = lean_usize_of_nat(x_287);
lean_dec(x_287);
x_289 = 0;
x_290 = x_4;
x_291 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_292 = l_Lean_nullKind___closed__2;
x_293 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_291, x_285, x_292, x_288, x_289, x_290);
x_294 = x_293;
x_295 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_296 = l_Lean_mkSepArray(x_294, x_295);
lean_dec(x_294);
x_297 = l_Array_appendCore___rarg(x_285, x_296);
lean_dec(x_296);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_292);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_array_push(x_286, x_298);
x_300 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_301 = lean_array_push(x_299, x_300);
x_302 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_281);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_array_push(x_301, x_303);
x_305 = lean_array_push(x_304, x_1);
x_306 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_282);
return x_308;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = l_myMacro____x40_Init_Notation___hyg_14520____closed__3;
lean_inc(x_1);
x_14 = lean_name_mk_string(x_1, x_13);
lean_inc(x_2);
lean_inc(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_2);
lean_inc(x_2);
x_16 = lean_array_push(x_2, x_15);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = 1;
x_20 = x_5 + x_19;
x_21 = x_18;
x_22 = lean_array_uset(x_11, x_5, x_21);
x_5 = x_20;
x_6 = x_22;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
x_11 = lean_nat_add(x_6, x_9);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_13);
lean_ctor_set(x_5, 2, x_6);
x_15 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(x_5, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkArrow___closed__2;
x_19 = l_Lean_addMacroScope(x_13, x_18, x_6);
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_inc(x_22);
x_23 = lean_array_push(x_4, x_22);
lean_inc(x_5);
x_24 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_23, x_5, x_17);
lean_dec(x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_5, x_26);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_29);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Array_empty___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_29);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_push(x_32, x_35);
x_37 = lean_array_push(x_32, x_22);
x_38 = l_Lean_nullKind___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_32, x_39);
x_41 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_40, x_42);
x_44 = lean_array_push(x_43, x_25);
x_45 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_push(x_36, x_46);
x_48 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_33, x_49);
x_51 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_27, 0, x_52);
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
x_55 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_53);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_empty___closed__1;
x_58 = lean_array_push(x_57, x_56);
x_59 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_53);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_push(x_57, x_60);
x_62 = lean_array_push(x_57, x_22);
x_63 = l_Lean_nullKind___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_57, x_64);
x_66 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_65, x_67);
x_69 = lean_array_push(x_68, x_25);
x_70 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_push(x_61, x_71);
x_73 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_array_push(x_58, x_74);
x_76 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_54);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_22);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_24);
if (x_79 == 0)
{
return x_24;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_24, 0);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_24);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_83 = lean_ctor_get(x_5, 0);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 3);
x_86 = lean_ctor_get(x_5, 4);
x_87 = lean_ctor_get(x_5, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_84);
x_88 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_6);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set(x_88, 4, x_86);
lean_ctor_set(x_88, 5, x_87);
x_89 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(x_88, x_11);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Meta_mkArrow___closed__2;
x_93 = l_Lean_addMacroScope(x_84, x_92, x_6);
x_94 = lean_box(0);
x_95 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_inc(x_96);
x_97 = lean_array_push(x_4, x_96);
lean_inc(x_88);
x_98 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_97, x_88, x_91);
lean_dec(x_10);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_88, x_100);
lean_dec(x_88);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Parser_Tactic_inductionAlt___closed__5;
lean_inc(x_102);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Array_empty___closed__1;
x_108 = lean_array_push(x_107, x_106);
x_109 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_102);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_102);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_push(x_107, x_110);
x_112 = lean_array_push(x_107, x_96);
x_113 = l_Lean_nullKind___closed__2;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_array_push(x_107, x_114);
x_116 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_array_push(x_115, x_117);
x_119 = lean_array_push(x_118, x_99);
x_120 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_111, x_121);
x_123 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_array_push(x_108, x_124);
x_126 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
if (lean_is_scalar(x_104)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_104;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_103);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_96);
lean_dec(x_88);
x_129 = lean_ctor_get(x_98, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_98, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_131 = x_98;
} else {
 lean_dec_ref(x_98);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(x_5, x_6);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = lean_ctor_get(x_133, 1);
x_137 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_135);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Array_empty___closed__1;
x_140 = lean_array_push(x_139, x_138);
x_141 = lean_array_get_size(x_4);
x_142 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_143 = 0;
x_144 = x_4;
x_145 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_146 = l_Lean_nullKind___closed__2;
x_147 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_145, x_139, x_146, x_142, x_143, x_144);
x_148 = x_147;
x_149 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_150 = l_Lean_mkSepArray(x_148, x_149);
lean_dec(x_148);
x_151 = l_Array_appendCore___rarg(x_139, x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_push(x_140, x_152);
x_154 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_155 = lean_array_push(x_153, x_154);
x_156 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_135);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_push(x_155, x_157);
x_159 = lean_array_push(x_158, x_1);
x_160 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = l_Lean_Syntax_isNone(x_2);
if (x_162 == 0)
{
lean_object* x_163; 
lean_free_object(x_133);
x_163 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_161, x_5, x_136);
return x_163;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_133, 0, x_161);
return x_133;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_164 = lean_ctor_get(x_133, 0);
x_165 = lean_ctor_get(x_133, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_133);
x_166 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_164);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Array_empty___closed__1;
x_169 = lean_array_push(x_168, x_167);
x_170 = lean_array_get_size(x_4);
x_171 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_172 = 0;
x_173 = x_4;
x_174 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_175 = l_Lean_nullKind___closed__2;
x_176 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_174, x_168, x_175, x_171, x_172, x_173);
x_177 = x_176;
x_178 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_179 = l_Lean_mkSepArray(x_177, x_178);
lean_dec(x_177);
x_180 = l_Array_appendCore___rarg(x_168, x_179);
lean_dec(x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_push(x_169, x_181);
x_183 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_184 = lean_array_push(x_182, x_183);
x_185 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_164);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_array_push(x_184, x_186);
x_188 = lean_array_push(x_187, x_1);
x_189 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l_Lean_Syntax_isNone(x_2);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_190, x_5, x_165);
return x_192;
}
else
{
lean_object* x_193; 
lean_dec(x_5);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_165);
return x_193;
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
lean_object* l_Lean_Elab_Term_elabFun_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Elab_Term_elabFun_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
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
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
lean_inc(x_14);
x_18 = l_Lean_Syntax_isOfKind(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_20 = lean_st_ref_get(x_8, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_7, 3);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_8, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_23);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_34, 0, x_23);
x_35 = x_34;
x_36 = lean_environment_main_module(x_23);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
lean_ctor_set(x_37, 5, x_24);
x_38 = 0;
x_39 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_14, x_38, x_37, x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_take(x_8, x_32);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_43, 1);
lean_dec(x_46);
lean_ctor_set(x_43, 1, x_41);
x_47 = lean_st_ref_set(x_8, x_43, x_44);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_40);
lean_inc(x_1);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_49, 0, x_1);
lean_closure_set(x_49, 1, x_40);
lean_closure_set(x_49, 2, x_2);
x_50 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_40, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 2);
x_53 = lean_ctor_get(x_43, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_8, x_54, x_44);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_40);
lean_inc(x_1);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_57, 0, x_1);
lean_closure_set(x_57, 1, x_40);
lean_closure_set(x_57, 2, x_2);
x_58 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_40, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_1);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Syntax_getArg(x_14, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = l_Lean_Syntax_getArg(x_14, x_61);
lean_dec(x_14);
x_63 = l_Lean_Syntax_getArgs(x_60);
lean_dec(x_60);
lean_inc(x_3);
x_64 = l_Lean_Elab_Term_expandFunBinders(x_63, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun_loop___lambda__1), 10, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = l_Lean_Elab_Term_elabFunBinders___rarg(x_70, x_2, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
lean_dec(x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_ctor_get(x_66, 0);
lean_inc(x_76);
lean_dec(x_66);
x_77 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_78);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Array_empty___closed__1;
x_87 = lean_array_push(x_86, x_85);
x_88 = l_Array_appendCore___rarg(x_86, x_75);
lean_dec(x_75);
x_89 = l_Lean_nullKind___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_86, x_90);
x_92 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_array_push(x_91, x_93);
x_95 = lean_array_push(x_94, x_76);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_15);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_87, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_10);
lean_ctor_set(x_98, 1, x_97);
x_1 = x_98;
x_9 = x_83;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabFun_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
x_3 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg___lambda__1), 9, 3);
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
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg), 11, 0);
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
x_28 = l_Lean_Meta_mkLambdaFVars(x_4, x_22, x_24, x_20, x_7, x_8, x_9, x_10, x_27);
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
x_19 = l_Lean_Meta_mkLambdaFVars(x_3, x_16, x_18, x_14, x_7, x_8, x_9, x_10, x_17);
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_7);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_Term_elabTerm(x_2, x_3, x_14, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_instantiateMVars(x_16, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_4);
x_23 = 0;
x_24 = l_Lean_Meta_mkLambdaFVars(x_22, x_19, x_23, x_14, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1090____closed__1;
x_2 = l_myMacro____x40_Init_Notation___hyg_16009____closed__1;
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_box(x_8);
lean_inc(x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed), 11, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_4);
x_18 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Elab_Term_elabBinders___rarg(x_2, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_50; lean_object* x_51; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_69 = lean_st_ref_get(x_14, x_22);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_50 = x_18;
x_51 = x_73;
goto block_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_76 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_75, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_50 = x_79;
x_51 = x_78;
goto block_68;
}
block_49:
{
if (x_7 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = l_Lean_Syntax_getId(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__4), 11, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_5);
lean_closure_set(x_28, 2, x_6);
x_29 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_23);
x_30 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_27, x_29, x_23, x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_24);
x_33 = l_Lean_mkApp(x_31, x_24);
x_34 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3(x_8, x_25, x_4, x_24, x_23, x_33, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Syntax_getId(x_1);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__4), 11, 3);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_5);
lean_closure_set(x_40, 2, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_24);
lean_inc(x_23);
x_41 = l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(x_39, x_23, x_24, x_40, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3(x_8, x_25, x_4, x_24, x_23, x_42, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
block_68:
{
if (x_50 == 0)
{
x_26 = x_51;
goto block_49;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_52 = l_Lean_Syntax_getId(x_1);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_KernelException_toMessageData___closed__15;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_23);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_23);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_24);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_24);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_54);
x_65 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_66 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_65, x_64, x_9, x_10, x_11, x_12, x_13, x_14, x_51);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_26 = x_67;
goto block_49;
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
x_80 = !lean_is_exclusive(x_19);
if (x_80 == 0)
{
return x_19;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_19, 0);
x_82 = lean_ctor_get(x_19, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_19);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
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
x_24 = l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
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
x_42 = l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
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
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_5, x_9);
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
x_3 = lean_unsigned_to_nat(583u);
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
x_27 = l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_34 = lean_st_ref_get(x_10, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_9, 3);
lean_inc(x_38);
x_39 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 2);
lean_inc(x_43);
x_44 = lean_st_ref_get(x_10, x_41);
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
x_52 = l_Lean_Elab_Term_expandLetEqnsDecl(x_23, x_51, x_47);
lean_dec(x_23);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_10, x_46);
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
x_60 = lean_st_ref_set(x_10, x_56, x_57);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_14 = x_53;
x_15 = x_61;
goto block_21;
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
x_66 = lean_st_ref_set(x_10, x_65, x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_14 = x_53;
x_15 = x_67;
goto block_21;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_26);
lean_dec(x_13);
x_68 = l_Lean_Syntax_getArg(x_23, x_22);
x_69 = lean_unsigned_to_nat(2u);
x_70 = l_Lean_Syntax_getArg(x_23, x_69);
x_71 = l_Lean_Elab_Term_expandOptType(x_1, x_70);
lean_dec(x_70);
x_72 = lean_unsigned_to_nat(4u);
x_73 = l_Lean_Syntax_getArg(x_23, x_72);
lean_dec(x_23);
x_74 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_11);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_myMacro____x40_Init_Notation___hyg_16009____closed__1;
lean_inc(x_75);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Array_empty___closed__1;
x_86 = lean_array_push(x_85, x_84);
x_87 = l_Lean_Meta_mkArrow___closed__2;
x_88 = l_Lean_addMacroScope(x_81, x_87, x_78);
x_89 = lean_box(0);
x_90 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_75);
x_91 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_91, 0, x_75);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_89);
lean_inc(x_91);
x_92 = lean_array_push(x_85, x_91);
x_93 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_94 = lean_array_push(x_92, x_93);
x_95 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_inc(x_75);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_75);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_85, x_96);
x_98 = lean_array_push(x_97, x_71);
x_99 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_array_push(x_85, x_100);
x_102 = l_Lean_nullKind___closed__2;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_array_push(x_94, x_103);
x_105 = l_myMacro____x40_Init_Notation___hyg_16009____closed__11;
lean_inc(x_75);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_75);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_104, x_106);
x_108 = lean_array_push(x_107, x_73);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_27);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_push(x_85, x_109);
x_111 = l_myMacro____x40_Init_Notation___hyg_16009____closed__4;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_array_push(x_86, x_112);
x_114 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_75);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_75);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_85, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_array_push(x_113, x_117);
x_119 = l_myMacro____x40_Init_Notation___hyg_14520____closed__1;
lean_inc(x_75);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_75);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_85, x_120);
x_122 = l_myMacro____x40_Init_Notation___hyg_14520____closed__5;
x_123 = lean_array_push(x_122, x_91);
x_124 = l_myMacro____x40_Init_Notation___hyg_14520____closed__4;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_push(x_85, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_102);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_array_push(x_121, x_127);
x_129 = lean_array_push(x_128, x_93);
x_130 = l_myMacro____x40_Init_Notation___hyg_14520____closed__6;
lean_inc(x_75);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_129, x_131);
x_133 = l_myMacro____x40_Init_Notation___hyg_14520____closed__11;
lean_inc(x_75);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_75);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_push(x_85, x_134);
x_136 = lean_array_push(x_85, x_68);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_102);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_array_push(x_135, x_137);
x_139 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_75);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_array_push(x_138, x_140);
x_142 = lean_array_push(x_141, x_25);
x_143 = l_myMacro____x40_Init_Notation___hyg_14520____closed__10;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_array_push(x_85, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_102);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_array_push(x_85, x_146);
x_148 = l_myMacro____x40_Init_Notation___hyg_14520____closed__8;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_array_push(x_132, x_149);
x_151 = l_myMacro____x40_Init_Notation___hyg_14520____closed__2;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_118, x_152);
x_154 = l_myMacro____x40_Init_Notation___hyg_16009____closed__2;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
if (x_3 == 0)
{
if (x_4 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
x_156 = l_Lean_instInhabitedSyntax;
x_157 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_158 = lean_panic_fn(x_156, x_157);
lean_inc(x_158);
lean_inc(x_1);
x_159 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_159, 0, x_1);
lean_closure_set(x_159, 1, x_158);
lean_closure_set(x_159, 2, x_2);
x_160 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_158, x_159, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
x_162 = l_Lean_Syntax_setKind(x_155, x_161);
lean_inc(x_162);
lean_inc(x_1);
x_163 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_163, 0, x_1);
lean_closure_set(x_163, 1, x_162);
lean_closure_set(x_163, 2, x_2);
x_164 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_162, x_163, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
return x_164;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_inc(x_155);
lean_inc(x_1);
x_165 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_165, 0, x_1);
lean_closure_set(x_165, 1, x_155);
lean_closure_set(x_165, 2, x_2);
x_166 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_155, x_165, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = l_Lean_Parser_Term_let__delayed___elambda__1___closed__2;
x_168 = l_Lean_Syntax_setKind(x_155, x_167);
lean_inc(x_168);
lean_inc(x_1);
x_169 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_169, 0, x_1);
lean_closure_set(x_169, 1, x_168);
lean_closure_set(x_169, 2, x_2);
x_170 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_168, x_169, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_1);
x_171 = l_Lean_Elab_Term_mkLetIdDeclView(x_23);
lean_dec(x_23);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
lean_dec(x_171);
x_176 = l_Lean_Elab_Term_elabLetDeclAux(x_172, x_173, x_174, x_175, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_176;
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
x_3 = l_myMacro____x40_Init_Notation___hyg_16009____closed__2;
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
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_5431_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabLetDeclAux___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
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
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___lambda__1___closed__6);
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
l_Lean_Elab_Term_expandWhereDecls___closed__2 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__2);
l_Lean_Elab_Term_expandWhereDecls___closed__3 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__3);
l_Lean_Elab_Term_expandWhereDecls___closed__4 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__4);
l_Lean_Elab_Term_expandWhereDecls___closed__5 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2);
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
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_5431_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
