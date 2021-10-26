// Lean compiler output
// Module: Lean.Elab.Binders
// Imports: Init Lean.Elab.Quotation.Precheck Lean.Elab.Term Lean.Elab.BindersUtil Lean.Parser.Term
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__9;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabArrow___closed__4;
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__2;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__12;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lean_Elab_Term_expandFunBinders_loop___spec__2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__1;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__11;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandFun(lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__4;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
static lean_object* l_Lean_Elab_Term_elabArrow___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__4;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__37;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__3;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__8;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object*);
static lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabArrow___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__6;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___closed__2;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__22;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__18;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__15;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLetFunAnnotation(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__42;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__46;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_expandFun___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_expandFun___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4___rarg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object*);
extern lean_object* l_Lean_nameLitKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__13;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__10;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__8;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__6;
lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__5;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow___closed__2;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__16;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabFun___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__4;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__30;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__33;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__28;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__3;
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__10;
static lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun___closed__2;
static lean_object* l_Lean_Elab_Term_elabForall___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabFun___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__47;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_6817_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431_(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__4;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__20;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__19;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__32;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__2;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabForall___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__24;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__7;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabForall(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__19;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Term_checkBinderAnnotations___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__7;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__5;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl(lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__26;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__5;
extern lean_object* l_Lean_identKind;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__5;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkBinderAnnotations;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__16;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__6;
lean_object* l_Lean_mkHole(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__35;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__39;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1;
lean_object* l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__31;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__6;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__12;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__10;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__41;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_expandFun___closed__3;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__10;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__23;
lean_object* l_Lean_Elab_Term_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__5;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__4;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__17;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__44;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__5;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___closed__4;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__17;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__8;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__11;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__3;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__43;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabLetDeclCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__18;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8;
lean_object* l_Array_sequenceMap___at___aux__Init__NotationExtra______macroRules___xabterm_x25_x5b___x7c___x5d_xbb__1___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__3;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__38;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_State_fvars___default;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__48;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__40;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__3;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__3;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__4;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__17;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__34;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__13;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__27;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Elab_Term_resolveName_x27___spec__3(lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__36;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_elabForall___closed__5;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_addMacroScope(x_10, x_1, x_14);
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
x_18 = l_Lean_addMacroScope(x_10, x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Syntax_isNone(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__3;
x_14 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_mkIdentFrom(x_1, x_16);
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
x_20 = l_Lean_mkIdentFrom(x_1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg___boxed), 3, 0);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array.push");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("push");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, antiquotation is not allowed");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_27; lean_object* x_63; lean_object* x_71; uint8_t x_72; 
x_19 = lean_array_uget(x_6, x_8);
x_71 = l_Lean_nullKind;
x_72 = lean_name_eq(x_1, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_27 = x_73;
goto block_62;
}
else
{
uint8_t x_74; 
x_74 = l_Lean_Syntax_isAntiquotSuffixSplice(x_19);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Syntax_isAntiquotSplice(x_19);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_27 = x_76;
goto block_62;
}
else
{
lean_object* x_77; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = lean_box(0);
x_63 = x_77;
goto block_70;
}
}
else
{
lean_object* x_78; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_box(0);
x_63 = x_78;
goto block_70;
}
}
block_26:
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_22;
x_16 = x_21;
goto _start;
}
block_62:
{
lean_object* x_28; 
lean_dec(x_27);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_28 = l_Lean_Elab_Term_quoteAutoTactic(x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_14);
x_31 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_14, x_15, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__6;
lean_inc(x_3);
x_41 = lean_name_mk_string(x_3, x_40);
lean_inc(x_41);
x_42 = l_Lean_addMacroScope(x_38, x_41, x_35);
lean_inc(x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_4);
lean_inc(x_5);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_5);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__5;
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_44);
x_47 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_48 = lean_array_push(x_47, x_9);
x_49 = lean_array_push(x_48, x_29);
x_50 = lean_box(2);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_49);
x_53 = lean_array_push(x_47, x_46);
x_54 = lean_array_push(x_53, x_52);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_20 = x_57;
x_21 = x_39;
goto block_26;
}
else
{
uint8_t x_58; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_28);
if (x_58 == 0)
{
return x_28;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_28, 0);
x_60 = lean_ctor_get(x_28, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_28);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_70:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_63);
x_64 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11;
x_65 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_19, x_64, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_19);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_1);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_8);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, tactic is missing");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array.empty");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Array");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
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
lean_object* x_1; 
x_1 = lean_mk_string("Syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("node");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__16;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SourceInfo.none");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__24;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SourceInfo");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("none");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__27;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__30;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__31;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quotedName");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__35;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAtom");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__40;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__40;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_quoteAutoTactic___closed__41;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__40;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__40;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__44;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__45;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid auto tactic, identifier is not allowed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__47;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Term_quoteAutoTactic___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lean_Syntax_isAntiquot(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_15 = lean_ctor_get(x_1, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = l_Lean_Elab_Term_instMonadQuotationTermElabM;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_6);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_6, x_7, x_8);
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
x_26 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_30 = l_Lean_addMacroScope(x_27, x_29, x_24);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_33 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_array_get_size(x_12);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_11, x_19, x_38, x_31, x_31, x_12, x_36, x_37, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_12);
lean_dec(x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_6);
x_42 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_6, x_7, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_47);
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
lean_inc(x_46);
lean_inc(x_50);
x_52 = l_Lean_addMacroScope(x_50, x_51, x_46);
x_53 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_54 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
lean_inc(x_43);
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_54);
x_56 = l_Lean_Elab_Term_quoteAutoTactic___closed__29;
x_57 = l_Lean_addMacroScope(x_50, x_56, x_46);
x_58 = l_Lean_Elab_Term_quoteAutoTactic___closed__25;
x_59 = l_Lean_Elab_Term_quoteAutoTactic___closed__33;
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
lean_inc(x_11);
x_61 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_31, x_11);
x_62 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_63 = lean_array_push(x_62, x_60);
x_64 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_65 = lean_array_push(x_64, x_55);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = l___private_Init_Meta_0__Lean_quoteNameMk(x_11);
x_67 = lean_array_push(x_63, x_66);
x_68 = lean_array_push(x_67, x_40);
x_69 = lean_box(2);
x_70 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_70);
lean_ctor_set(x_1, 0, x_69);
x_71 = lean_array_push(x_65, x_1);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_48, 0, x_73);
return x_48;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = l_Lean_Elab_Term_quoteAutoTactic___closed__37;
x_76 = l_String_intercalate(x_75, x_74);
x_77 = l_Lean_Elab_Term_quoteAutoTactic___closed__38;
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
x_79 = l_Lean_nameLitKind;
x_80 = lean_box(2);
x_81 = l_Lean_Syntax_mkLit(x_79, x_78, x_80);
x_82 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_83 = lean_array_push(x_82, x_81);
x_84 = l_Lean_Elab_Term_quoteAutoTactic___closed__36;
lean_ctor_set(x_1, 2, x_83);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_80);
x_85 = lean_array_push(x_63, x_1);
x_86 = lean_array_push(x_85, x_40);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_86);
x_89 = lean_array_push(x_65, x_88);
x_90 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_48, 0, x_91);
return x_48;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_92 = lean_ctor_get(x_48, 0);
x_93 = lean_ctor_get(x_48, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_48);
x_94 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
lean_inc(x_46);
lean_inc(x_92);
x_95 = l_Lean_addMacroScope(x_92, x_94, x_46);
x_96 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_97 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
lean_inc(x_43);
x_98 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_98, 0, x_43);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_97);
x_99 = l_Lean_Elab_Term_quoteAutoTactic___closed__29;
x_100 = l_Lean_addMacroScope(x_92, x_99, x_46);
x_101 = l_Lean_Elab_Term_quoteAutoTactic___closed__25;
x_102 = l_Lean_Elab_Term_quoteAutoTactic___closed__33;
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_43);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_102);
lean_inc(x_11);
x_104 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_31, x_11);
x_105 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_106 = lean_array_push(x_105, x_103);
x_107 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_108 = lean_array_push(x_107, x_98);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = l___private_Init_Meta_0__Lean_quoteNameMk(x_11);
x_110 = lean_array_push(x_106, x_109);
x_111 = lean_array_push(x_110, x_40);
x_112 = lean_box(2);
x_113 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_113);
lean_ctor_set(x_1, 0, x_112);
x_114 = lean_array_push(x_108, x_1);
x_115 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_93);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_11);
x_118 = lean_ctor_get(x_104, 0);
lean_inc(x_118);
lean_dec(x_104);
x_119 = l_Lean_Elab_Term_quoteAutoTactic___closed__37;
x_120 = l_String_intercalate(x_119, x_118);
x_121 = l_Lean_Elab_Term_quoteAutoTactic___closed__38;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = l_Lean_nameLitKind;
x_124 = lean_box(2);
x_125 = l_Lean_Syntax_mkLit(x_123, x_122, x_124);
x_126 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_127 = lean_array_push(x_126, x_125);
x_128 = l_Lean_Elab_Term_quoteAutoTactic___closed__36;
lean_ctor_set(x_1, 2, x_127);
lean_ctor_set(x_1, 1, x_128);
lean_ctor_set(x_1, 0, x_124);
x_129 = lean_array_push(x_106, x_1);
x_130 = lean_array_push(x_129, x_40);
x_131 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_130);
x_133 = lean_array_push(x_108, x_132);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_124);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_93);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_39);
if (x_137 == 0)
{
return x_39;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_39, 0);
x_139 = lean_ctor_get(x_39, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_39);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; size_t x_159; size_t x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_1);
x_141 = l_Lean_Elab_Term_instMonadQuotationTermElabM;
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_inc(x_6);
x_143 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_6, x_7, x_8);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_153 = l_Lean_addMacroScope(x_150, x_152, x_147);
x_154 = lean_box(0);
x_155 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_156 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_157 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_157, 0, x_144);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_157, 2, x_153);
lean_ctor_set(x_157, 3, x_156);
x_158 = lean_array_get_size(x_12);
x_159 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_160 = 0;
x_161 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_162 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_11, x_142, x_161, x_154, x_154, x_12, x_159, x_160, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_151);
lean_dec(x_12);
lean_dec(x_142);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_6);
x_165 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_6, x_7, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_167);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_170);
lean_dec(x_7);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
lean_inc(x_169);
lean_inc(x_172);
x_176 = l_Lean_addMacroScope(x_172, x_175, x_169);
x_177 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_178 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
lean_inc(x_166);
x_179 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_179, 0, x_166);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_176);
lean_ctor_set(x_179, 3, x_178);
x_180 = l_Lean_Elab_Term_quoteAutoTactic___closed__29;
x_181 = l_Lean_addMacroScope(x_172, x_180, x_169);
x_182 = l_Lean_Elab_Term_quoteAutoTactic___closed__25;
x_183 = l_Lean_Elab_Term_quoteAutoTactic___closed__33;
x_184 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_184, 0, x_166);
lean_ctor_set(x_184, 1, x_182);
lean_ctor_set(x_184, 2, x_181);
lean_ctor_set(x_184, 3, x_183);
lean_inc(x_11);
x_185 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_154, x_11);
x_186 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_187 = lean_array_push(x_186, x_184);
x_188 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_189 = lean_array_push(x_188, x_179);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_190 = l___private_Init_Meta_0__Lean_quoteNameMk(x_11);
x_191 = lean_array_push(x_187, x_190);
x_192 = lean_array_push(x_191, x_163);
x_193 = lean_box(2);
x_194 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_192);
x_196 = lean_array_push(x_189, x_195);
x_197 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_196);
if (lean_is_scalar(x_174)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_174;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_173);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_11);
x_200 = lean_ctor_get(x_185, 0);
lean_inc(x_200);
lean_dec(x_185);
x_201 = l_Lean_Elab_Term_quoteAutoTactic___closed__37;
x_202 = l_String_intercalate(x_201, x_200);
x_203 = l_Lean_Elab_Term_quoteAutoTactic___closed__38;
x_204 = lean_string_append(x_203, x_202);
lean_dec(x_202);
x_205 = l_Lean_nameLitKind;
x_206 = lean_box(2);
x_207 = l_Lean_Syntax_mkLit(x_205, x_204, x_206);
x_208 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_209 = lean_array_push(x_208, x_207);
x_210 = l_Lean_Elab_Term_quoteAutoTactic___closed__36;
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_206);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_209);
x_212 = lean_array_push(x_187, x_211);
x_213 = lean_array_push(x_212, x_163);
x_214 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_213);
x_216 = lean_array_push(x_189, x_215);
x_217 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_206);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_216);
if (lean_is_scalar(x_174)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_174;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_173);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_220 = lean_ctor_get(x_162, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_162, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_222 = x_162;
} else {
 lean_dec_ref(x_162);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_12);
lean_dec(x_11);
x_224 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11;
x_225 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_1, x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_225;
}
}
case 2:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_226 = lean_ctor_get(x_1, 1);
lean_inc(x_226);
lean_dec(x_1);
lean_inc(x_6);
x_227 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_6, x_7, x_8);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_229);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_232);
lean_dec(x_7);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = l_Lean_Elab_Term_quoteAutoTactic___closed__43;
x_237 = l_Lean_addMacroScope(x_235, x_236, x_231);
x_238 = l_Lean_Elab_Term_quoteAutoTactic___closed__42;
x_239 = l_Lean_Elab_Term_quoteAutoTactic___closed__46;
x_240 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_240, 0, x_228);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_240, 2, x_237);
lean_ctor_set(x_240, 3, x_239);
x_241 = lean_box(2);
x_242 = l_Lean_Syntax_mkStrLit(x_226, x_241);
lean_dec(x_226);
x_243 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_244 = lean_array_push(x_243, x_242);
x_245 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_246 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_244);
x_247 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_248 = lean_array_push(x_247, x_240);
x_249 = lean_array_push(x_248, x_246);
x_250 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_251 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_251, 0, x_241);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_249);
lean_ctor_set(x_233, 0, x_251);
return x_233;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_252 = lean_ctor_get(x_233, 0);
x_253 = lean_ctor_get(x_233, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_233);
x_254 = l_Lean_Elab_Term_quoteAutoTactic___closed__43;
x_255 = l_Lean_addMacroScope(x_252, x_254, x_231);
x_256 = l_Lean_Elab_Term_quoteAutoTactic___closed__42;
x_257 = l_Lean_Elab_Term_quoteAutoTactic___closed__46;
x_258 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_258, 0, x_228);
lean_ctor_set(x_258, 1, x_256);
lean_ctor_set(x_258, 2, x_255);
lean_ctor_set(x_258, 3, x_257);
x_259 = lean_box(2);
x_260 = l_Lean_Syntax_mkStrLit(x_226, x_259);
lean_dec(x_226);
x_261 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_262 = lean_array_push(x_261, x_260);
x_263 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_259);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_262);
x_265 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_266 = lean_array_push(x_265, x_258);
x_267 = lean_array_push(x_266, x_264);
x_268 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_259);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_269, 2, x_267);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_253);
return x_270;
}
}
default: 
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_Elab_Term_quoteAutoTactic___closed__48;
x_272 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_1, x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_272;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_17);
x_18 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
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
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("autoParam");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4;
x_2 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_addMacroScope(x_11, x_1, x_14);
x_17 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_quoteAutoTactic(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__2;
x_22 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Elab_Term_elabTerm(x_19, x_21, x_22, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Meta_instantiateMVars(x_24, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__6;
x_42 = lean_st_ref_get(x_8, x_28);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = 0;
x_30 = x_47;
x_31 = x_46;
goto block_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_30 = x_52;
x_31 = x_51;
goto block_41;
}
block_41:
{
if (x_30 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1;
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Term_declareTacticSyntax___lambda__1(x_16, x_17, x_32, x_27, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_27);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_27);
x_36 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_29, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1;
x_40 = l_Lean_Elab_Term_declareTacticSyntax___lambda__1(x_16, x_17, x_39, x_27, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_37);
return x_40;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
return x_26;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
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
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_23);
if (x_57 == 0)
{
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Term_declareTacticSyntax___closed__2;
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_declareTacticSyntax___lambda__2), 9, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_declareTacticSyntax___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_1; 
x_1 = lean_mk_string("binderDefault");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binderTactic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5;
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
x_2 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optParam");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__11;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__2;
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__4;
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
lean_inc(x_7);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_7, x_8, x_23);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
x_34 = l_Lean_addMacroScope(x_32, x_33, x_28);
x_35 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
x_36 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9;
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Lean_mkIdentFrom(x_20, x_22);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_40 = lean_array_push(x_39, x_1);
x_41 = lean_array_push(x_40, x_38);
x_42 = lean_box(2);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
x_45 = lean_array_push(x_39, x_37);
x_46 = lean_array_push(x_45, x_44);
x_47 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_30, 0, x_48);
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__7;
x_52 = l_Lean_addMacroScope(x_49, x_51, x_28);
x_53 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__6;
x_54 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9;
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_54);
x_56 = l_Lean_mkIdentFrom(x_20, x_22);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_58 = lean_array_push(x_57, x_1);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_box(2);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_59);
x_63 = lean_array_push(x_57, x_55);
x_64 = lean_array_push(x_63, x_62);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_50);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_21;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_13);
x_72 = lean_unsigned_to_nat(1u);
x_73 = l_Lean_Syntax_getArg(x_12, x_72);
lean_dec(x_12);
lean_inc(x_7);
x_74 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_7, x_8, x_9);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_79);
lean_dec(x_8);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13;
x_84 = l_Lean_addMacroScope(x_82, x_83, x_78);
x_85 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12;
x_86 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15;
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_86);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_89 = lean_array_push(x_88, x_1);
x_90 = lean_array_push(x_89, x_73);
x_91 = lean_box(2);
x_92 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_90);
x_94 = lean_array_push(x_88, x_87);
x_95 = lean_array_push(x_94, x_93);
x_96 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_80, 0, x_97);
return x_80;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_98 = lean_ctor_get(x_80, 0);
x_99 = lean_ctor_get(x_80, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_80);
x_100 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13;
x_101 = l_Lean_addMacroScope(x_98, x_100, x_78);
x_102 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12;
x_103 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_75);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_103);
x_105 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_106 = lean_array_push(x_105, x_1);
x_107 = lean_array_push(x_106, x_73);
x_108 = lean_box(2);
x_109 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_107);
x_111 = lean_array_push(x_105, x_104);
x_112 = lean_array_push(x_111, x_110);
x_113 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_99);
return x_115;
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8;
x_22 = lean_name_eq(x_18, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2;
x_24 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_17, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_30 = lean_usize_add(x_2, x_29);
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
x_35 = lean_usize_add(x_2, x_34);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_inc(x_18);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_18, x_1);
x_23 = 2;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = x_24;
x_28 = lean_array_uset(x_17, x_3, x_27);
x_3 = x_26;
x_4 = x_28;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_inc(x_18);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_18, x_1);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = x_24;
x_28 = lean_array_uset(x_17, x_3, x_27);
x_3 = x_26;
x_4 = x_28;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = x_5;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_5, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_5, x_4, x_17);
x_19 = x_16;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_19, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(x_23, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_4, x_29);
x_31 = x_28;
x_32 = lean_array_uset(x_18, x_4, x_31);
x_4 = x_30;
x_5 = x_32;
x_12 = x_26;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_inc(x_18);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_expandOptType(x_18, x_1);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = x_24;
x_28 = lean_array_uset(x_17, x_3, x_27);
x_3 = x_26;
x_4 = x_28;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simpleBinder");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitBinder");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("implicitBinder");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strictImplicitBinder");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instBinder");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_9 = l_Lean_Syntax_getKind(x_1);
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__2;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__4;
x_13 = lean_name_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__6;
x_15 = lean_name_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__8;
x_17 = lean_name_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__10;
x_19 = lean_name_eq(x_9, x_18);
lean_dec(x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___rarg(x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unsigned_to_nat(2u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
lean_dec(x_1);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
x_30 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
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
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
lean_dec(x_1);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_36);
x_38 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
x_45 = lean_unsigned_to_nat(1u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
lean_dec(x_1);
x_52 = lean_array_get_size(x_48);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = x_48;
x_55 = lean_box_usize(x_53);
x_56 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_57 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed), 11, 4);
lean_closure_set(x_57, 0, x_51);
lean_closure_set(x_57, 1, x_55);
lean_closure_set(x_57, 2, x_56);
lean_closure_set(x_57, 3, x_54);
x_58 = x_57;
x_59 = lean_apply_7(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_49);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_9);
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(2u);
x_70 = l_Lean_Syntax_getArg(x_1, x_69);
lean_dec(x_1);
x_71 = lean_array_get_size(x_67);
x_72 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_73 = x_67;
x_74 = lean_box_usize(x_72);
x_75 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_76 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed), 11, 4);
lean_closure_set(x_76, 0, x_70);
lean_closure_set(x_76, 1, x_74);
lean_closure_set(x_76, 2, x_75);
lean_closure_set(x_76, 3, x_73);
x_77 = x_76;
x_78 = lean_apply_7(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_68);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
return x_66;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_66, 0);
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_66);
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
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_9);
x_83 = lean_unsigned_to_nat(1u);
x_84 = l_Lean_Syntax_getArg(x_1, x_83);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_85 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(2u);
x_89 = l_Lean_Syntax_getArg(x_1, x_88);
x_90 = lean_unsigned_to_nat(3u);
x_91 = l_Lean_Syntax_getArg(x_1, x_90);
lean_dec(x_1);
x_92 = lean_array_get_size(x_86);
x_93 = lean_usize_of_nat(x_92);
lean_dec(x_92);
x_94 = x_86;
x_95 = lean_box_usize(x_93);
x_96 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_97 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed), 12, 5);
lean_closure_set(x_97, 0, x_89);
lean_closure_set(x_97, 1, x_91);
lean_closure_set(x_97, 2, x_95);
lean_closure_set(x_97, 3, x_96);
lean_closure_set(x_97, 4, x_94);
x_98 = x_97;
x_99 = lean_apply_7(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_87);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_85, 0);
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_9);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_106 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unsigned_to_nat(1u);
x_110 = l_Lean_Syntax_getArg(x_1, x_109);
lean_dec(x_1);
x_111 = lean_array_get_size(x_107);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = x_107;
x_114 = lean_box_usize(x_112);
x_115 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___boxed__const__1;
x_116 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__5___boxed), 11, 4);
lean_closure_set(x_116, 0, x_110);
lean_closure_set(x_116, 1, x_114);
lean_closure_set(x_116, 2, x_115);
lean_closure_set(x_116, 3, x_113);
x_117 = x_116;
x_118 = lean_apply_7(x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_108);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
return x_106;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_106, 0);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_106);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___closed__3;
x_11 = l_Lean_Elab_Term_registerCustomErrorIfMVar(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = 1;
x_13 = l_Lean_Elab_Term_addTermInfo(x_1, x_2, x_10, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_18 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16(x_9, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkBinderAnnotations");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("check whether type is a class instance whenever the binder annotation `[...]` is used");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__2;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__5;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_checkBinderAnnotations___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_18 = lean_array_push(x_3, x_6);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_4, x_5, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
else
{
uint8_t x_20; 
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
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getId(x_15);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__1), 13, 5);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___rarg(x_1, x_3, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_14 = lean_apply_1(x_2, x_13);
x_15 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabBinder___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_Elab_Term_elabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forall");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabForall___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabForall___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_2 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabForall");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabForall___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arrow");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabArrow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_elabArrow___closed__2;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_elabType(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Elab_Term_elabType(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Elab_Term_elabArrow___closed__4;
x_30 = l_Lean_addMacroScope(x_24, x_29, x_28);
x_31 = 0;
x_32 = l_Lean_mkForall(x_30, x_31, x_18, x_21);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = l_Lean_Elab_Term_elabArrow___closed__4;
x_36 = l_Lean_addMacroScope(x_24, x_35, x_33);
x_37 = 0;
x_38 = l_Lean_mkForall(x_36, x_37, x_18, x_21);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabArrow");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabArrow___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrow___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabArrow___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_15 = lean_array_push(x_14, x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___lambda__1), 9, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = l_Lean_Elab_Term_elabBinders___rarg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_1 = lean_mk_string("depArrow");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDepArrow");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
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
x_18 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
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
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7;
lean_inc(x_1);
x_23 = lean_name_mk_string(x_1, x_22);
lean_inc(x_21);
x_24 = l_Lean_Syntax_isOfKind(x_21, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2;
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
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_5 = x_13;
x_7 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2;
lean_inc(x_1);
x_20 = l_Lean_Syntax_isOfKind(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8;
lean_inc(x_1);
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_23 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2;
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
x_68 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8;
lean_inc(x_34);
x_69 = l_Lean_Syntax_isOfKind(x_34, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2;
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
x_43 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_44 = lean_array_push(x_43, x_42);
x_45 = lean_array_get_size(x_37);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
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
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
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
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lean_Elab_Term_expandFunBinders_loop___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
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
x_17 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
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
x_13 = lean_usize_add(x_3, x_12);
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchDiscr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlt");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("|");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=>");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeAscription");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_32 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_26);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_34);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_38 = lean_array_push(x_37, x_16);
x_39 = lean_box(2);
x_40 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_38);
x_42 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_43);
x_46 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_34);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_34);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_42, x_14);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_50);
x_52 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_55 = lean_array_push(x_54, x_49);
x_56 = lean_array_push(x_55, x_51);
x_57 = lean_array_push(x_56, x_53);
x_58 = lean_array_push(x_57, x_30);
x_59 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_39);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_58);
x_61 = lean_array_push(x_42, x_60);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_array_push(x_42, x_62);
x_64 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_39);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
x_66 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_67 = lean_array_push(x_66, x_36);
x_68 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_array_push(x_69, x_45);
x_71 = lean_array_push(x_70, x_68);
x_72 = lean_array_push(x_71, x_47);
x_73 = lean_array_push(x_72, x_65);
x_74 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_39);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_73);
x_76 = 1;
x_77 = lean_box(x_76);
lean_ctor_set(x_25, 1, x_77);
lean_ctor_set(x_25, 0, x_75);
lean_ctor_set(x_32, 0, x_24);
return x_32;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
x_78 = lean_ctor_get(x_32, 0);
x_79 = lean_ctor_get(x_32, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_32);
x_80 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_78);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_83 = lean_array_push(x_82, x_16);
x_84 = lean_box(2);
x_85 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_83);
x_87 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_88 = lean_array_push(x_87, x_86);
x_89 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_88);
x_91 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_78);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_78);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_78);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_array_push(x_87, x_14);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_95);
x_97 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_78);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_100 = lean_array_push(x_99, x_94);
x_101 = lean_array_push(x_100, x_96);
x_102 = lean_array_push(x_101, x_98);
x_103 = lean_array_push(x_102, x_30);
x_104 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_84);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_103);
x_106 = lean_array_push(x_87, x_105);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_84);
lean_ctor_set(x_107, 1, x_89);
lean_ctor_set(x_107, 2, x_106);
x_108 = lean_array_push(x_87, x_107);
x_109 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_84);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
x_111 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_112 = lean_array_push(x_111, x_81);
x_113 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_114 = lean_array_push(x_112, x_113);
x_115 = lean_array_push(x_114, x_90);
x_116 = lean_array_push(x_115, x_113);
x_117 = lean_array_push(x_116, x_92);
x_118 = lean_array_push(x_117, x_110);
x_119 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_84);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_118);
x_121 = 1;
x_122 = lean_box(x_121);
lean_ctor_set(x_25, 1, x_122);
lean_ctor_set(x_25, 0, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_24);
lean_ctor_set(x_123, 1, x_79);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_124 = lean_ctor_get(x_25, 0);
lean_inc(x_124);
lean_dec(x_25);
x_125 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_26);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_126);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_132 = lean_array_push(x_131, x_16);
x_133 = lean_box(2);
x_134 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_132);
x_136 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_137 = lean_array_push(x_136, x_135);
x_138 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
x_140 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_126);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_126);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_126);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_126);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_array_push(x_136, x_14);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_133);
lean_ctor_set(x_145, 1, x_138);
lean_ctor_set(x_145, 2, x_144);
x_146 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_126);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_149 = lean_array_push(x_148, x_143);
x_150 = lean_array_push(x_149, x_145);
x_151 = lean_array_push(x_150, x_147);
x_152 = lean_array_push(x_151, x_124);
x_153 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_133);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_152);
x_155 = lean_array_push(x_136, x_154);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_133);
lean_ctor_set(x_156, 1, x_138);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_array_push(x_136, x_156);
x_158 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_133);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_157);
x_160 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_161 = lean_array_push(x_160, x_130);
x_162 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_163 = lean_array_push(x_161, x_162);
x_164 = lean_array_push(x_163, x_139);
x_165 = lean_array_push(x_164, x_162);
x_166 = lean_array_push(x_165, x_141);
x_167 = lean_array_push(x_166, x_159);
x_168 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_133);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_167);
x_170 = 1;
x_171 = lean_box(x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_24, 1, x_172);
if (lean_is_scalar(x_128)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_128;
}
lean_ctor_set(x_173, 0, x_24);
lean_ctor_set(x_173, 1, x_127);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_174 = lean_ctor_get(x_24, 0);
lean_inc(x_174);
lean_dec(x_24);
x_175 = lean_ctor_get(x_25, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_176 = x_25;
} else {
 lean_dec_ref(x_25);
 x_176 = lean_box(0);
}
x_177 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_26);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
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
x_181 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_178);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_184 = lean_array_push(x_183, x_16);
x_185 = lean_box(2);
x_186 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_184);
x_188 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_189 = lean_array_push(x_188, x_187);
x_190 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set(x_191, 2, x_189);
x_192 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_178);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_178);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_178);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_178);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_array_push(x_188, x_14);
x_197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_197, 0, x_185);
lean_ctor_set(x_197, 1, x_190);
lean_ctor_set(x_197, 2, x_196);
x_198 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_178);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_201 = lean_array_push(x_200, x_195);
x_202 = lean_array_push(x_201, x_197);
x_203 = lean_array_push(x_202, x_199);
x_204 = lean_array_push(x_203, x_175);
x_205 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_206 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_206, 0, x_185);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_204);
x_207 = lean_array_push(x_188, x_206);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_185);
lean_ctor_set(x_208, 1, x_190);
lean_ctor_set(x_208, 2, x_207);
x_209 = lean_array_push(x_188, x_208);
x_210 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_185);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_209);
x_212 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_213 = lean_array_push(x_212, x_182);
x_214 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_215 = lean_array_push(x_213, x_214);
x_216 = lean_array_push(x_215, x_191);
x_217 = lean_array_push(x_216, x_214);
x_218 = lean_array_push(x_217, x_193);
x_219 = lean_array_push(x_218, x_211);
x_220 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_221 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_221, 0, x_185);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_219);
x_222 = 1;
x_223 = lean_box(x_222);
if (lean_is_scalar(x_176)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_176;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_174);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_180)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_180;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_179);
return x_226;
}
}
case 1:
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_14, 1);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 1)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
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
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_dec(x_227);
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_dec(x_229);
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_dec(x_230);
x_236 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_237 = lean_string_dec_eq(x_235, x_236);
lean_dec(x_235);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_inc(x_5);
lean_inc(x_14);
x_238 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_3, x_241);
lean_dec(x_3);
lean_inc(x_14);
x_243 = l_Lean_mkHole(x_14);
lean_inc(x_239);
x_244 = l_Lean_Elab_Term_mkExplicitBinder(x_239, x_243);
x_245 = lean_array_push(x_4, x_244);
lean_inc(x_5);
x_246 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_242, x_245, x_5, x_240);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = !lean_is_exclusive(x_247);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_247, 1);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_248);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_253 = lean_ctor_get(x_248, 0);
x_254 = lean_ctor_get(x_248, 1);
lean_dec(x_254);
x_255 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_249);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_257);
x_259 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_261 = lean_array_push(x_260, x_239);
x_262 = lean_box(2);
x_263 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_261);
x_265 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_266 = lean_array_push(x_265, x_264);
x_267 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_268 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_268, 0, x_262);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_268, 2, x_266);
x_269 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_257);
x_270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_270, 0, x_257);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_257);
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_257);
lean_ctor_set(x_272, 1, x_271);
lean_inc(x_14);
x_273 = lean_array_push(x_265, x_14);
x_274 = !lean_is_exclusive(x_14);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; 
x_275 = lean_ctor_get(x_14, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_14, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_14, 0);
lean_dec(x_277);
lean_ctor_set(x_14, 2, x_273);
lean_ctor_set(x_14, 1, x_267);
lean_ctor_set(x_14, 0, x_262);
x_278 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_257);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_281 = lean_array_push(x_280, x_272);
x_282 = lean_array_push(x_281, x_14);
x_283 = lean_array_push(x_282, x_279);
x_284 = lean_array_push(x_283, x_253);
x_285 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_286 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_286, 0, x_262);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set(x_286, 2, x_284);
x_287 = lean_array_push(x_265, x_286);
x_288 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_288, 0, x_262);
lean_ctor_set(x_288, 1, x_267);
lean_ctor_set(x_288, 2, x_287);
x_289 = lean_array_push(x_265, x_288);
x_290 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_291 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_291, 0, x_262);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_291, 2, x_289);
x_292 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_293 = lean_array_push(x_292, x_259);
x_294 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_295 = lean_array_push(x_293, x_294);
x_296 = lean_array_push(x_295, x_268);
x_297 = lean_array_push(x_296, x_294);
x_298 = lean_array_push(x_297, x_270);
x_299 = lean_array_push(x_298, x_291);
x_300 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_301 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_301, 0, x_262);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set(x_301, 2, x_299);
x_302 = 1;
x_303 = lean_box(x_302);
lean_ctor_set(x_248, 1, x_303);
lean_ctor_set(x_248, 0, x_301);
lean_ctor_set(x_255, 0, x_247);
return x_255;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; 
lean_dec(x_14);
x_304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_304, 0, x_262);
lean_ctor_set(x_304, 1, x_267);
lean_ctor_set(x_304, 2, x_273);
x_305 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_257);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_308 = lean_array_push(x_307, x_272);
x_309 = lean_array_push(x_308, x_304);
x_310 = lean_array_push(x_309, x_306);
x_311 = lean_array_push(x_310, x_253);
x_312 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_313 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_313, 0, x_262);
lean_ctor_set(x_313, 1, x_312);
lean_ctor_set(x_313, 2, x_311);
x_314 = lean_array_push(x_265, x_313);
x_315 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_315, 0, x_262);
lean_ctor_set(x_315, 1, x_267);
lean_ctor_set(x_315, 2, x_314);
x_316 = lean_array_push(x_265, x_315);
x_317 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_318 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_318, 0, x_262);
lean_ctor_set(x_318, 1, x_317);
lean_ctor_set(x_318, 2, x_316);
x_319 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_320 = lean_array_push(x_319, x_259);
x_321 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_322 = lean_array_push(x_320, x_321);
x_323 = lean_array_push(x_322, x_268);
x_324 = lean_array_push(x_323, x_321);
x_325 = lean_array_push(x_324, x_270);
x_326 = lean_array_push(x_325, x_318);
x_327 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_262);
lean_ctor_set(x_328, 1, x_327);
lean_ctor_set(x_328, 2, x_326);
x_329 = 1;
x_330 = lean_box(x_329);
lean_ctor_set(x_248, 1, x_330);
lean_ctor_set(x_248, 0, x_328);
lean_ctor_set(x_255, 0, x_247);
return x_255;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; 
x_331 = lean_ctor_get(x_255, 0);
x_332 = lean_ctor_get(x_255, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_255);
x_333 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_331);
x_334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_336 = lean_array_push(x_335, x_239);
x_337 = lean_box(2);
x_338 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
lean_ctor_set(x_339, 2, x_336);
x_340 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_341 = lean_array_push(x_340, x_339);
x_342 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_343 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_343, 0, x_337);
lean_ctor_set(x_343, 1, x_342);
lean_ctor_set(x_343, 2, x_341);
x_344 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_331);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_331);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_331);
x_347 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_347, 0, x_331);
lean_ctor_set(x_347, 1, x_346);
lean_inc(x_14);
x_348 = lean_array_push(x_340, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_349 = x_14;
} else {
 lean_dec_ref(x_14);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 3, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_337);
lean_ctor_set(x_350, 1, x_342);
lean_ctor_set(x_350, 2, x_348);
x_351 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_352 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_352, 0, x_331);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_354 = lean_array_push(x_353, x_347);
x_355 = lean_array_push(x_354, x_350);
x_356 = lean_array_push(x_355, x_352);
x_357 = lean_array_push(x_356, x_253);
x_358 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_359 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_359, 0, x_337);
lean_ctor_set(x_359, 1, x_358);
lean_ctor_set(x_359, 2, x_357);
x_360 = lean_array_push(x_340, x_359);
x_361 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_361, 0, x_337);
lean_ctor_set(x_361, 1, x_342);
lean_ctor_set(x_361, 2, x_360);
x_362 = lean_array_push(x_340, x_361);
x_363 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_364 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_364, 0, x_337);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set(x_364, 2, x_362);
x_365 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_366 = lean_array_push(x_365, x_334);
x_367 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_368 = lean_array_push(x_366, x_367);
x_369 = lean_array_push(x_368, x_343);
x_370 = lean_array_push(x_369, x_367);
x_371 = lean_array_push(x_370, x_345);
x_372 = lean_array_push(x_371, x_364);
x_373 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_337);
lean_ctor_set(x_374, 1, x_373);
lean_ctor_set(x_374, 2, x_372);
x_375 = 1;
x_376 = lean_box(x_375);
lean_ctor_set(x_248, 1, x_376);
lean_ctor_set(x_248, 0, x_374);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_247);
lean_ctor_set(x_377, 1, x_332);
return x_377;
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_378 = lean_ctor_get(x_248, 0);
lean_inc(x_378);
lean_dec(x_248);
x_379 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_249);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_382 = x_379;
} else {
 lean_dec_ref(x_379);
 x_382 = lean_box(0);
}
x_383 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_380);
x_384 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_384, 0, x_380);
lean_ctor_set(x_384, 1, x_383);
x_385 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_386 = lean_array_push(x_385, x_239);
x_387 = lean_box(2);
x_388 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_389 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
lean_ctor_set(x_389, 2, x_386);
x_390 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_391 = lean_array_push(x_390, x_389);
x_392 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_393 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_393, 0, x_387);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set(x_393, 2, x_391);
x_394 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_380);
x_395 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_395, 0, x_380);
lean_ctor_set(x_395, 1, x_394);
x_396 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_380);
x_397 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_397, 0, x_380);
lean_ctor_set(x_397, 1, x_396);
lean_inc(x_14);
x_398 = lean_array_push(x_390, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_399 = x_14;
} else {
 lean_dec_ref(x_14);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 3, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_387);
lean_ctor_set(x_400, 1, x_392);
lean_ctor_set(x_400, 2, x_398);
x_401 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_402 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_402, 0, x_380);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_404 = lean_array_push(x_403, x_397);
x_405 = lean_array_push(x_404, x_400);
x_406 = lean_array_push(x_405, x_402);
x_407 = lean_array_push(x_406, x_378);
x_408 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_409 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_409, 0, x_387);
lean_ctor_set(x_409, 1, x_408);
lean_ctor_set(x_409, 2, x_407);
x_410 = lean_array_push(x_390, x_409);
x_411 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_411, 0, x_387);
lean_ctor_set(x_411, 1, x_392);
lean_ctor_set(x_411, 2, x_410);
x_412 = lean_array_push(x_390, x_411);
x_413 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_414 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_414, 0, x_387);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set(x_414, 2, x_412);
x_415 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_416 = lean_array_push(x_415, x_384);
x_417 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_418 = lean_array_push(x_416, x_417);
x_419 = lean_array_push(x_418, x_393);
x_420 = lean_array_push(x_419, x_417);
x_421 = lean_array_push(x_420, x_395);
x_422 = lean_array_push(x_421, x_414);
x_423 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_424 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_424, 0, x_387);
lean_ctor_set(x_424, 1, x_423);
lean_ctor_set(x_424, 2, x_422);
x_425 = 1;
x_426 = lean_box(x_425);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_247, 1, x_427);
if (lean_is_scalar(x_382)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_382;
}
lean_ctor_set(x_428, 0, x_247);
lean_ctor_set(x_428, 1, x_381);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_429 = lean_ctor_get(x_247, 0);
lean_inc(x_429);
lean_dec(x_247);
x_430 = lean_ctor_get(x_248, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_431 = x_248;
} else {
 lean_dec_ref(x_248);
 x_431 = lean_box(0);
}
x_432 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_249);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
x_436 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_433);
x_437 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_436);
x_438 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_439 = lean_array_push(x_438, x_239);
x_440 = lean_box(2);
x_441 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_442 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
lean_ctor_set(x_442, 2, x_439);
x_443 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_444 = lean_array_push(x_443, x_442);
x_445 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_446 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_446, 0, x_440);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set(x_446, 2, x_444);
x_447 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_433);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_433);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_433);
x_450 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_450, 0, x_433);
lean_ctor_set(x_450, 1, x_449);
lean_inc(x_14);
x_451 = lean_array_push(x_443, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_452 = x_14;
} else {
 lean_dec_ref(x_14);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 3, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_440);
lean_ctor_set(x_453, 1, x_445);
lean_ctor_set(x_453, 2, x_451);
x_454 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_433);
lean_ctor_set(x_455, 1, x_454);
x_456 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_457 = lean_array_push(x_456, x_450);
x_458 = lean_array_push(x_457, x_453);
x_459 = lean_array_push(x_458, x_455);
x_460 = lean_array_push(x_459, x_430);
x_461 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_462 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_462, 0, x_440);
lean_ctor_set(x_462, 1, x_461);
lean_ctor_set(x_462, 2, x_460);
x_463 = lean_array_push(x_443, x_462);
x_464 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_464, 0, x_440);
lean_ctor_set(x_464, 1, x_445);
lean_ctor_set(x_464, 2, x_463);
x_465 = lean_array_push(x_443, x_464);
x_466 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_467 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_467, 0, x_440);
lean_ctor_set(x_467, 1, x_466);
lean_ctor_set(x_467, 2, x_465);
x_468 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_469 = lean_array_push(x_468, x_437);
x_470 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_471 = lean_array_push(x_469, x_470);
x_472 = lean_array_push(x_471, x_446);
x_473 = lean_array_push(x_472, x_470);
x_474 = lean_array_push(x_473, x_448);
x_475 = lean_array_push(x_474, x_467);
x_476 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_477 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_477, 0, x_440);
lean_ctor_set(x_477, 1, x_476);
lean_ctor_set(x_477, 2, x_475);
x_478 = 1;
x_479 = lean_box(x_478);
if (lean_is_scalar(x_431)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_431;
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_479);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_429);
lean_ctor_set(x_481, 1, x_480);
if (lean_is_scalar(x_435)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_435;
}
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_434);
return x_482;
}
}
else
{
lean_object* x_483; uint8_t x_484; 
x_483 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3;
x_484 = lean_string_dec_eq(x_234, x_483);
lean_dec(x_234);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
lean_dec(x_233);
lean_dec(x_232);
lean_inc(x_5);
lean_inc(x_14);
x_485 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_unsigned_to_nat(1u);
x_489 = lean_nat_add(x_3, x_488);
lean_dec(x_3);
lean_inc(x_14);
x_490 = l_Lean_mkHole(x_14);
lean_inc(x_486);
x_491 = l_Lean_Elab_Term_mkExplicitBinder(x_486, x_490);
x_492 = lean_array_push(x_4, x_491);
lean_inc(x_5);
x_493 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_489, x_492, x_5, x_487);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_493, 1);
lean_inc(x_496);
lean_dec(x_493);
x_497 = !lean_is_exclusive(x_494);
if (x_497 == 0)
{
lean_object* x_498; uint8_t x_499; 
x_498 = lean_ctor_get(x_494, 1);
lean_dec(x_498);
x_499 = !lean_is_exclusive(x_495);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_500 = lean_ctor_get(x_495, 0);
x_501 = lean_ctor_get(x_495, 1);
lean_dec(x_501);
x_502 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_496);
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_504 = lean_ctor_get(x_502, 0);
x_505 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_504);
x_506 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_507 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_508 = lean_array_push(x_507, x_486);
x_509 = lean_box(2);
x_510 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_511 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
lean_ctor_set(x_511, 2, x_508);
x_512 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_513 = lean_array_push(x_512, x_511);
x_514 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_515 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_515, 0, x_509);
lean_ctor_set(x_515, 1, x_514);
lean_ctor_set(x_515, 2, x_513);
x_516 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_504);
x_517 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_517, 0, x_504);
lean_ctor_set(x_517, 1, x_516);
x_518 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_504);
x_519 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_519, 0, x_504);
lean_ctor_set(x_519, 1, x_518);
lean_inc(x_14);
x_520 = lean_array_push(x_512, x_14);
x_521 = !lean_is_exclusive(x_14);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; lean_object* x_550; 
x_522 = lean_ctor_get(x_14, 2);
lean_dec(x_522);
x_523 = lean_ctor_get(x_14, 1);
lean_dec(x_523);
x_524 = lean_ctor_get(x_14, 0);
lean_dec(x_524);
lean_ctor_set(x_14, 2, x_520);
lean_ctor_set(x_14, 1, x_514);
lean_ctor_set(x_14, 0, x_509);
x_525 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_526 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_526, 0, x_504);
lean_ctor_set(x_526, 1, x_525);
x_527 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_528 = lean_array_push(x_527, x_519);
x_529 = lean_array_push(x_528, x_14);
x_530 = lean_array_push(x_529, x_526);
x_531 = lean_array_push(x_530, x_500);
x_532 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_533 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_533, 0, x_509);
lean_ctor_set(x_533, 1, x_532);
lean_ctor_set(x_533, 2, x_531);
x_534 = lean_array_push(x_512, x_533);
x_535 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_535, 0, x_509);
lean_ctor_set(x_535, 1, x_514);
lean_ctor_set(x_535, 2, x_534);
x_536 = lean_array_push(x_512, x_535);
x_537 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_538 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_538, 0, x_509);
lean_ctor_set(x_538, 1, x_537);
lean_ctor_set(x_538, 2, x_536);
x_539 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_540 = lean_array_push(x_539, x_506);
x_541 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_542 = lean_array_push(x_540, x_541);
x_543 = lean_array_push(x_542, x_515);
x_544 = lean_array_push(x_543, x_541);
x_545 = lean_array_push(x_544, x_517);
x_546 = lean_array_push(x_545, x_538);
x_547 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_548 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_548, 0, x_509);
lean_ctor_set(x_548, 1, x_547);
lean_ctor_set(x_548, 2, x_546);
x_549 = 1;
x_550 = lean_box(x_549);
lean_ctor_set(x_495, 1, x_550);
lean_ctor_set(x_495, 0, x_548);
lean_ctor_set(x_502, 0, x_494);
return x_502;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; 
lean_dec(x_14);
x_551 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_551, 0, x_509);
lean_ctor_set(x_551, 1, x_514);
lean_ctor_set(x_551, 2, x_520);
x_552 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_553 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_553, 0, x_504);
lean_ctor_set(x_553, 1, x_552);
x_554 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_555 = lean_array_push(x_554, x_519);
x_556 = lean_array_push(x_555, x_551);
x_557 = lean_array_push(x_556, x_553);
x_558 = lean_array_push(x_557, x_500);
x_559 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_560 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_560, 0, x_509);
lean_ctor_set(x_560, 1, x_559);
lean_ctor_set(x_560, 2, x_558);
x_561 = lean_array_push(x_512, x_560);
x_562 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_562, 0, x_509);
lean_ctor_set(x_562, 1, x_514);
lean_ctor_set(x_562, 2, x_561);
x_563 = lean_array_push(x_512, x_562);
x_564 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_565 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_565, 0, x_509);
lean_ctor_set(x_565, 1, x_564);
lean_ctor_set(x_565, 2, x_563);
x_566 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_567 = lean_array_push(x_566, x_506);
x_568 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_569 = lean_array_push(x_567, x_568);
x_570 = lean_array_push(x_569, x_515);
x_571 = lean_array_push(x_570, x_568);
x_572 = lean_array_push(x_571, x_517);
x_573 = lean_array_push(x_572, x_565);
x_574 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_575 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_575, 0, x_509);
lean_ctor_set(x_575, 1, x_574);
lean_ctor_set(x_575, 2, x_573);
x_576 = 1;
x_577 = lean_box(x_576);
lean_ctor_set(x_495, 1, x_577);
lean_ctor_set(x_495, 0, x_575);
lean_ctor_set(x_502, 0, x_494);
return x_502;
}
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; uint8_t x_622; lean_object* x_623; lean_object* x_624; 
x_578 = lean_ctor_get(x_502, 0);
x_579 = lean_ctor_get(x_502, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_502);
x_580 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_578);
x_581 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_583 = lean_array_push(x_582, x_486);
x_584 = lean_box(2);
x_585 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_586 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
lean_ctor_set(x_586, 2, x_583);
x_587 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_588 = lean_array_push(x_587, x_586);
x_589 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_590 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_590, 0, x_584);
lean_ctor_set(x_590, 1, x_589);
lean_ctor_set(x_590, 2, x_588);
x_591 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_578);
x_592 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_592, 0, x_578);
lean_ctor_set(x_592, 1, x_591);
x_593 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_578);
x_594 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_594, 0, x_578);
lean_ctor_set(x_594, 1, x_593);
lean_inc(x_14);
x_595 = lean_array_push(x_587, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_596 = x_14;
} else {
 lean_dec_ref(x_14);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 3, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_584);
lean_ctor_set(x_597, 1, x_589);
lean_ctor_set(x_597, 2, x_595);
x_598 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_599 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_599, 0, x_578);
lean_ctor_set(x_599, 1, x_598);
x_600 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_601 = lean_array_push(x_600, x_594);
x_602 = lean_array_push(x_601, x_597);
x_603 = lean_array_push(x_602, x_599);
x_604 = lean_array_push(x_603, x_500);
x_605 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_606 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_606, 0, x_584);
lean_ctor_set(x_606, 1, x_605);
lean_ctor_set(x_606, 2, x_604);
x_607 = lean_array_push(x_587, x_606);
x_608 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_608, 0, x_584);
lean_ctor_set(x_608, 1, x_589);
lean_ctor_set(x_608, 2, x_607);
x_609 = lean_array_push(x_587, x_608);
x_610 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_611 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_611, 0, x_584);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_611, 2, x_609);
x_612 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_613 = lean_array_push(x_612, x_581);
x_614 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_615 = lean_array_push(x_613, x_614);
x_616 = lean_array_push(x_615, x_590);
x_617 = lean_array_push(x_616, x_614);
x_618 = lean_array_push(x_617, x_592);
x_619 = lean_array_push(x_618, x_611);
x_620 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_621 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_621, 0, x_584);
lean_ctor_set(x_621, 1, x_620);
lean_ctor_set(x_621, 2, x_619);
x_622 = 1;
x_623 = lean_box(x_622);
lean_ctor_set(x_495, 1, x_623);
lean_ctor_set(x_495, 0, x_621);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_494);
lean_ctor_set(x_624, 1, x_579);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_625 = lean_ctor_get(x_495, 0);
lean_inc(x_625);
lean_dec(x_495);
x_626 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_496);
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
x_630 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_627);
x_631 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_631, 0, x_627);
lean_ctor_set(x_631, 1, x_630);
x_632 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_633 = lean_array_push(x_632, x_486);
x_634 = lean_box(2);
x_635 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_636 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
lean_ctor_set(x_636, 2, x_633);
x_637 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_638 = lean_array_push(x_637, x_636);
x_639 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_640 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_640, 0, x_634);
lean_ctor_set(x_640, 1, x_639);
lean_ctor_set(x_640, 2, x_638);
x_641 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_627);
x_642 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_642, 0, x_627);
lean_ctor_set(x_642, 1, x_641);
x_643 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_627);
x_644 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_644, 0, x_627);
lean_ctor_set(x_644, 1, x_643);
lean_inc(x_14);
x_645 = lean_array_push(x_637, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_646 = x_14;
} else {
 lean_dec_ref(x_14);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 3, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_634);
lean_ctor_set(x_647, 1, x_639);
lean_ctor_set(x_647, 2, x_645);
x_648 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_649 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_649, 0, x_627);
lean_ctor_set(x_649, 1, x_648);
x_650 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_651 = lean_array_push(x_650, x_644);
x_652 = lean_array_push(x_651, x_647);
x_653 = lean_array_push(x_652, x_649);
x_654 = lean_array_push(x_653, x_625);
x_655 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_656 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_656, 0, x_634);
lean_ctor_set(x_656, 1, x_655);
lean_ctor_set(x_656, 2, x_654);
x_657 = lean_array_push(x_637, x_656);
x_658 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_658, 0, x_634);
lean_ctor_set(x_658, 1, x_639);
lean_ctor_set(x_658, 2, x_657);
x_659 = lean_array_push(x_637, x_658);
x_660 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_661 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_661, 0, x_634);
lean_ctor_set(x_661, 1, x_660);
lean_ctor_set(x_661, 2, x_659);
x_662 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_663 = lean_array_push(x_662, x_631);
x_664 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_665 = lean_array_push(x_663, x_664);
x_666 = lean_array_push(x_665, x_640);
x_667 = lean_array_push(x_666, x_664);
x_668 = lean_array_push(x_667, x_642);
x_669 = lean_array_push(x_668, x_661);
x_670 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_671 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_671, 0, x_634);
lean_ctor_set(x_671, 1, x_670);
lean_ctor_set(x_671, 2, x_669);
x_672 = 1;
x_673 = lean_box(x_672);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_673);
lean_ctor_set(x_494, 1, x_674);
if (lean_is_scalar(x_629)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_629;
}
lean_ctor_set(x_675, 0, x_494);
lean_ctor_set(x_675, 1, x_628);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_676 = lean_ctor_get(x_494, 0);
lean_inc(x_676);
lean_dec(x_494);
x_677 = lean_ctor_get(x_495, 0);
lean_inc(x_677);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_678 = x_495;
} else {
 lean_dec_ref(x_495);
 x_678 = lean_box(0);
}
x_679 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_496);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_682 = x_679;
} else {
 lean_dec_ref(x_679);
 x_682 = lean_box(0);
}
x_683 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_680);
x_684 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_684, 0, x_680);
lean_ctor_set(x_684, 1, x_683);
x_685 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_686 = lean_array_push(x_685, x_486);
x_687 = lean_box(2);
x_688 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_689 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
lean_ctor_set(x_689, 2, x_686);
x_690 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_691 = lean_array_push(x_690, x_689);
x_692 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_693 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_693, 0, x_687);
lean_ctor_set(x_693, 1, x_692);
lean_ctor_set(x_693, 2, x_691);
x_694 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_680);
x_695 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_695, 0, x_680);
lean_ctor_set(x_695, 1, x_694);
x_696 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_680);
x_697 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_697, 0, x_680);
lean_ctor_set(x_697, 1, x_696);
lean_inc(x_14);
x_698 = lean_array_push(x_690, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_699 = x_14;
} else {
 lean_dec_ref(x_14);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 3, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_687);
lean_ctor_set(x_700, 1, x_692);
lean_ctor_set(x_700, 2, x_698);
x_701 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_702 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_702, 0, x_680);
lean_ctor_set(x_702, 1, x_701);
x_703 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_704 = lean_array_push(x_703, x_697);
x_705 = lean_array_push(x_704, x_700);
x_706 = lean_array_push(x_705, x_702);
x_707 = lean_array_push(x_706, x_677);
x_708 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_709 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_709, 0, x_687);
lean_ctor_set(x_709, 1, x_708);
lean_ctor_set(x_709, 2, x_707);
x_710 = lean_array_push(x_690, x_709);
x_711 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_711, 0, x_687);
lean_ctor_set(x_711, 1, x_692);
lean_ctor_set(x_711, 2, x_710);
x_712 = lean_array_push(x_690, x_711);
x_713 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_714 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_714, 0, x_687);
lean_ctor_set(x_714, 1, x_713);
lean_ctor_set(x_714, 2, x_712);
x_715 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_716 = lean_array_push(x_715, x_684);
x_717 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_718 = lean_array_push(x_716, x_717);
x_719 = lean_array_push(x_718, x_693);
x_720 = lean_array_push(x_719, x_717);
x_721 = lean_array_push(x_720, x_695);
x_722 = lean_array_push(x_721, x_714);
x_723 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_724 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_724, 0, x_687);
lean_ctor_set(x_724, 1, x_723);
lean_ctor_set(x_724, 2, x_722);
x_725 = 1;
x_726 = lean_box(x_725);
if (lean_is_scalar(x_678)) {
 x_727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_727 = x_678;
}
lean_ctor_set(x_727, 0, x_724);
lean_ctor_set(x_727, 1, x_726);
x_728 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_728, 0, x_676);
lean_ctor_set(x_728, 1, x_727);
if (lean_is_scalar(x_682)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_682;
}
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_681);
return x_729;
}
}
else
{
lean_object* x_730; uint8_t x_731; 
x_730 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5;
x_731 = lean_string_dec_eq(x_233, x_730);
lean_dec(x_233);
if (x_731 == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; 
lean_dec(x_232);
lean_inc(x_5);
lean_inc(x_14);
x_732 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = lean_unsigned_to_nat(1u);
x_736 = lean_nat_add(x_3, x_735);
lean_dec(x_3);
lean_inc(x_14);
x_737 = l_Lean_mkHole(x_14);
lean_inc(x_733);
x_738 = l_Lean_Elab_Term_mkExplicitBinder(x_733, x_737);
x_739 = lean_array_push(x_4, x_738);
lean_inc(x_5);
x_740 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_736, x_739, x_5, x_734);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_741, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_740, 1);
lean_inc(x_743);
lean_dec(x_740);
x_744 = !lean_is_exclusive(x_741);
if (x_744 == 0)
{
lean_object* x_745; uint8_t x_746; 
x_745 = lean_ctor_get(x_741, 1);
lean_dec(x_745);
x_746 = !lean_is_exclusive(x_742);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; 
x_747 = lean_ctor_get(x_742, 0);
x_748 = lean_ctor_get(x_742, 1);
lean_dec(x_748);
x_749 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_743);
x_750 = !lean_is_exclusive(x_749);
if (x_750 == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; uint8_t x_768; 
x_751 = lean_ctor_get(x_749, 0);
x_752 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_751);
x_753 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
x_754 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_755 = lean_array_push(x_754, x_733);
x_756 = lean_box(2);
x_757 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_758 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_758, 0, x_756);
lean_ctor_set(x_758, 1, x_757);
lean_ctor_set(x_758, 2, x_755);
x_759 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_760 = lean_array_push(x_759, x_758);
x_761 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_762 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_762, 0, x_756);
lean_ctor_set(x_762, 1, x_761);
lean_ctor_set(x_762, 2, x_760);
x_763 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_751);
x_764 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_764, 0, x_751);
lean_ctor_set(x_764, 1, x_763);
x_765 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_751);
x_766 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_766, 0, x_751);
lean_ctor_set(x_766, 1, x_765);
lean_inc(x_14);
x_767 = lean_array_push(x_759, x_14);
x_768 = !lean_is_exclusive(x_14);
if (x_768 == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; uint8_t x_796; lean_object* x_797; 
x_769 = lean_ctor_get(x_14, 2);
lean_dec(x_769);
x_770 = lean_ctor_get(x_14, 1);
lean_dec(x_770);
x_771 = lean_ctor_get(x_14, 0);
lean_dec(x_771);
lean_ctor_set(x_14, 2, x_767);
lean_ctor_set(x_14, 1, x_761);
lean_ctor_set(x_14, 0, x_756);
x_772 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_773 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_773, 0, x_751);
lean_ctor_set(x_773, 1, x_772);
x_774 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_775 = lean_array_push(x_774, x_766);
x_776 = lean_array_push(x_775, x_14);
x_777 = lean_array_push(x_776, x_773);
x_778 = lean_array_push(x_777, x_747);
x_779 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_780 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_780, 0, x_756);
lean_ctor_set(x_780, 1, x_779);
lean_ctor_set(x_780, 2, x_778);
x_781 = lean_array_push(x_759, x_780);
x_782 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_782, 0, x_756);
lean_ctor_set(x_782, 1, x_761);
lean_ctor_set(x_782, 2, x_781);
x_783 = lean_array_push(x_759, x_782);
x_784 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_785 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_785, 0, x_756);
lean_ctor_set(x_785, 1, x_784);
lean_ctor_set(x_785, 2, x_783);
x_786 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_787 = lean_array_push(x_786, x_753);
x_788 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_789 = lean_array_push(x_787, x_788);
x_790 = lean_array_push(x_789, x_762);
x_791 = lean_array_push(x_790, x_788);
x_792 = lean_array_push(x_791, x_764);
x_793 = lean_array_push(x_792, x_785);
x_794 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_795 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_795, 0, x_756);
lean_ctor_set(x_795, 1, x_794);
lean_ctor_set(x_795, 2, x_793);
x_796 = 1;
x_797 = lean_box(x_796);
lean_ctor_set(x_742, 1, x_797);
lean_ctor_set(x_742, 0, x_795);
lean_ctor_set(x_749, 0, x_741);
return x_749;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; lean_object* x_824; 
lean_dec(x_14);
x_798 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_798, 0, x_756);
lean_ctor_set(x_798, 1, x_761);
lean_ctor_set(x_798, 2, x_767);
x_799 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_800 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_800, 0, x_751);
lean_ctor_set(x_800, 1, x_799);
x_801 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_802 = lean_array_push(x_801, x_766);
x_803 = lean_array_push(x_802, x_798);
x_804 = lean_array_push(x_803, x_800);
x_805 = lean_array_push(x_804, x_747);
x_806 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_807 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_807, 0, x_756);
lean_ctor_set(x_807, 1, x_806);
lean_ctor_set(x_807, 2, x_805);
x_808 = lean_array_push(x_759, x_807);
x_809 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_809, 0, x_756);
lean_ctor_set(x_809, 1, x_761);
lean_ctor_set(x_809, 2, x_808);
x_810 = lean_array_push(x_759, x_809);
x_811 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_812 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_812, 0, x_756);
lean_ctor_set(x_812, 1, x_811);
lean_ctor_set(x_812, 2, x_810);
x_813 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_814 = lean_array_push(x_813, x_753);
x_815 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_816 = lean_array_push(x_814, x_815);
x_817 = lean_array_push(x_816, x_762);
x_818 = lean_array_push(x_817, x_815);
x_819 = lean_array_push(x_818, x_764);
x_820 = lean_array_push(x_819, x_812);
x_821 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_822 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_822, 0, x_756);
lean_ctor_set(x_822, 1, x_821);
lean_ctor_set(x_822, 2, x_820);
x_823 = 1;
x_824 = lean_box(x_823);
lean_ctor_set(x_742, 1, x_824);
lean_ctor_set(x_742, 0, x_822);
lean_ctor_set(x_749, 0, x_741);
return x_749;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; lean_object* x_870; lean_object* x_871; 
x_825 = lean_ctor_get(x_749, 0);
x_826 = lean_ctor_get(x_749, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_749);
x_827 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_825);
x_828 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_828, 0, x_825);
lean_ctor_set(x_828, 1, x_827);
x_829 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_830 = lean_array_push(x_829, x_733);
x_831 = lean_box(2);
x_832 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_833 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_833, 0, x_831);
lean_ctor_set(x_833, 1, x_832);
lean_ctor_set(x_833, 2, x_830);
x_834 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_835 = lean_array_push(x_834, x_833);
x_836 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_837 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_837, 0, x_831);
lean_ctor_set(x_837, 1, x_836);
lean_ctor_set(x_837, 2, x_835);
x_838 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_825);
x_839 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_839, 0, x_825);
lean_ctor_set(x_839, 1, x_838);
x_840 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_825);
x_841 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_841, 0, x_825);
lean_ctor_set(x_841, 1, x_840);
lean_inc(x_14);
x_842 = lean_array_push(x_834, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_843 = x_14;
} else {
 lean_dec_ref(x_14);
 x_843 = lean_box(0);
}
if (lean_is_scalar(x_843)) {
 x_844 = lean_alloc_ctor(1, 3, 0);
} else {
 x_844 = x_843;
}
lean_ctor_set(x_844, 0, x_831);
lean_ctor_set(x_844, 1, x_836);
lean_ctor_set(x_844, 2, x_842);
x_845 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_846 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_846, 0, x_825);
lean_ctor_set(x_846, 1, x_845);
x_847 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_848 = lean_array_push(x_847, x_841);
x_849 = lean_array_push(x_848, x_844);
x_850 = lean_array_push(x_849, x_846);
x_851 = lean_array_push(x_850, x_747);
x_852 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_853 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_853, 0, x_831);
lean_ctor_set(x_853, 1, x_852);
lean_ctor_set(x_853, 2, x_851);
x_854 = lean_array_push(x_834, x_853);
x_855 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_855, 0, x_831);
lean_ctor_set(x_855, 1, x_836);
lean_ctor_set(x_855, 2, x_854);
x_856 = lean_array_push(x_834, x_855);
x_857 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_858 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_858, 0, x_831);
lean_ctor_set(x_858, 1, x_857);
lean_ctor_set(x_858, 2, x_856);
x_859 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_860 = lean_array_push(x_859, x_828);
x_861 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_862 = lean_array_push(x_860, x_861);
x_863 = lean_array_push(x_862, x_837);
x_864 = lean_array_push(x_863, x_861);
x_865 = lean_array_push(x_864, x_839);
x_866 = lean_array_push(x_865, x_858);
x_867 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_868 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_868, 0, x_831);
lean_ctor_set(x_868, 1, x_867);
lean_ctor_set(x_868, 2, x_866);
x_869 = 1;
x_870 = lean_box(x_869);
lean_ctor_set(x_742, 1, x_870);
lean_ctor_set(x_742, 0, x_868);
x_871 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_871, 0, x_741);
lean_ctor_set(x_871, 1, x_826);
return x_871;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; uint8_t x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_872 = lean_ctor_get(x_742, 0);
lean_inc(x_872);
lean_dec(x_742);
x_873 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_743);
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
x_877 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_874);
x_878 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_878, 0, x_874);
lean_ctor_set(x_878, 1, x_877);
x_879 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_880 = lean_array_push(x_879, x_733);
x_881 = lean_box(2);
x_882 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_883 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
lean_ctor_set(x_883, 2, x_880);
x_884 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_885 = lean_array_push(x_884, x_883);
x_886 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_887 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_887, 0, x_881);
lean_ctor_set(x_887, 1, x_886);
lean_ctor_set(x_887, 2, x_885);
x_888 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_874);
x_889 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_889, 0, x_874);
lean_ctor_set(x_889, 1, x_888);
x_890 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_874);
x_891 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_891, 0, x_874);
lean_ctor_set(x_891, 1, x_890);
lean_inc(x_14);
x_892 = lean_array_push(x_884, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_893 = x_14;
} else {
 lean_dec_ref(x_14);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(1, 3, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_881);
lean_ctor_set(x_894, 1, x_886);
lean_ctor_set(x_894, 2, x_892);
x_895 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_896 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_896, 0, x_874);
lean_ctor_set(x_896, 1, x_895);
x_897 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_898 = lean_array_push(x_897, x_891);
x_899 = lean_array_push(x_898, x_894);
x_900 = lean_array_push(x_899, x_896);
x_901 = lean_array_push(x_900, x_872);
x_902 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_903 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_903, 0, x_881);
lean_ctor_set(x_903, 1, x_902);
lean_ctor_set(x_903, 2, x_901);
x_904 = lean_array_push(x_884, x_903);
x_905 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_905, 0, x_881);
lean_ctor_set(x_905, 1, x_886);
lean_ctor_set(x_905, 2, x_904);
x_906 = lean_array_push(x_884, x_905);
x_907 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_908 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_908, 0, x_881);
lean_ctor_set(x_908, 1, x_907);
lean_ctor_set(x_908, 2, x_906);
x_909 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_910 = lean_array_push(x_909, x_878);
x_911 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_912 = lean_array_push(x_910, x_911);
x_913 = lean_array_push(x_912, x_887);
x_914 = lean_array_push(x_913, x_911);
x_915 = lean_array_push(x_914, x_889);
x_916 = lean_array_push(x_915, x_908);
x_917 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_918 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_918, 0, x_881);
lean_ctor_set(x_918, 1, x_917);
lean_ctor_set(x_918, 2, x_916);
x_919 = 1;
x_920 = lean_box(x_919);
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_918);
lean_ctor_set(x_921, 1, x_920);
lean_ctor_set(x_741, 1, x_921);
if (lean_is_scalar(x_876)) {
 x_922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_922 = x_876;
}
lean_ctor_set(x_922, 0, x_741);
lean_ctor_set(x_922, 1, x_875);
return x_922;
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_923 = lean_ctor_get(x_741, 0);
lean_inc(x_923);
lean_dec(x_741);
x_924 = lean_ctor_get(x_742, 0);
lean_inc(x_924);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_925 = x_742;
} else {
 lean_dec_ref(x_742);
 x_925 = lean_box(0);
}
x_926 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_743);
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_929 = x_926;
} else {
 lean_dec_ref(x_926);
 x_929 = lean_box(0);
}
x_930 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_927);
x_931 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_931, 0, x_927);
lean_ctor_set(x_931, 1, x_930);
x_932 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_933 = lean_array_push(x_932, x_733);
x_934 = lean_box(2);
x_935 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_936 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_936, 0, x_934);
lean_ctor_set(x_936, 1, x_935);
lean_ctor_set(x_936, 2, x_933);
x_937 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_938 = lean_array_push(x_937, x_936);
x_939 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_940 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_940, 0, x_934);
lean_ctor_set(x_940, 1, x_939);
lean_ctor_set(x_940, 2, x_938);
x_941 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_927);
x_942 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_942, 0, x_927);
lean_ctor_set(x_942, 1, x_941);
x_943 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_927);
x_944 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_944, 0, x_927);
lean_ctor_set(x_944, 1, x_943);
lean_inc(x_14);
x_945 = lean_array_push(x_937, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_946 = x_14;
} else {
 lean_dec_ref(x_14);
 x_946 = lean_box(0);
}
if (lean_is_scalar(x_946)) {
 x_947 = lean_alloc_ctor(1, 3, 0);
} else {
 x_947 = x_946;
}
lean_ctor_set(x_947, 0, x_934);
lean_ctor_set(x_947, 1, x_939);
lean_ctor_set(x_947, 2, x_945);
x_948 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_949 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_949, 0, x_927);
lean_ctor_set(x_949, 1, x_948);
x_950 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_951 = lean_array_push(x_950, x_944);
x_952 = lean_array_push(x_951, x_947);
x_953 = lean_array_push(x_952, x_949);
x_954 = lean_array_push(x_953, x_924);
x_955 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_956 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_956, 0, x_934);
lean_ctor_set(x_956, 1, x_955);
lean_ctor_set(x_956, 2, x_954);
x_957 = lean_array_push(x_937, x_956);
x_958 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_958, 0, x_934);
lean_ctor_set(x_958, 1, x_939);
lean_ctor_set(x_958, 2, x_957);
x_959 = lean_array_push(x_937, x_958);
x_960 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_961 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_961, 0, x_934);
lean_ctor_set(x_961, 1, x_960);
lean_ctor_set(x_961, 2, x_959);
x_962 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_963 = lean_array_push(x_962, x_931);
x_964 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_965 = lean_array_push(x_963, x_964);
x_966 = lean_array_push(x_965, x_940);
x_967 = lean_array_push(x_966, x_964);
x_968 = lean_array_push(x_967, x_942);
x_969 = lean_array_push(x_968, x_961);
x_970 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_971 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_971, 0, x_934);
lean_ctor_set(x_971, 1, x_970);
lean_ctor_set(x_971, 2, x_969);
x_972 = 1;
x_973 = lean_box(x_972);
if (lean_is_scalar(x_925)) {
 x_974 = lean_alloc_ctor(0, 2, 0);
} else {
 x_974 = x_925;
}
lean_ctor_set(x_974, 0, x_971);
lean_ctor_set(x_974, 1, x_973);
x_975 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_975, 0, x_923);
lean_ctor_set(x_975, 1, x_974);
if (lean_is_scalar(x_929)) {
 x_976 = lean_alloc_ctor(0, 2, 0);
} else {
 x_976 = x_929;
}
lean_ctor_set(x_976, 0, x_975);
lean_ctor_set(x_976, 1, x_928);
return x_976;
}
}
else
{
lean_object* x_977; uint8_t x_978; 
x_977 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5;
x_978 = lean_string_dec_eq(x_232, x_977);
if (x_978 == 0)
{
lean_object* x_979; uint8_t x_980; 
x_979 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7;
x_980 = lean_string_dec_eq(x_232, x_979);
if (x_980 == 0)
{
lean_object* x_981; uint8_t x_982; 
x_981 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9;
x_982 = lean_string_dec_eq(x_232, x_981);
if (x_982 == 0)
{
lean_object* x_983; uint8_t x_984; 
x_983 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3;
x_984 = lean_string_dec_eq(x_232, x_983);
if (x_984 == 0)
{
lean_object* x_985; uint8_t x_986; 
x_985 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1;
x_986 = lean_string_dec_eq(x_232, x_985);
if (x_986 == 0)
{
lean_object* x_987; uint8_t x_988; 
x_987 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7;
x_988 = lean_string_dec_eq(x_232, x_987);
if (x_988 == 0)
{
lean_object* x_989; uint8_t x_990; 
x_989 = l_Lean_Elab_Term_expandFunBinders_loop___closed__16;
x_990 = lean_string_dec_eq(x_232, x_989);
lean_dec(x_232);
if (x_990 == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; 
lean_inc(x_5);
lean_inc(x_14);
x_991 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec(x_991);
x_994 = lean_unsigned_to_nat(1u);
x_995 = lean_nat_add(x_3, x_994);
lean_dec(x_3);
lean_inc(x_14);
x_996 = l_Lean_mkHole(x_14);
lean_inc(x_992);
x_997 = l_Lean_Elab_Term_mkExplicitBinder(x_992, x_996);
x_998 = lean_array_push(x_4, x_997);
lean_inc(x_5);
x_999 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_995, x_998, x_5, x_993);
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_1000, 1);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_999, 1);
lean_inc(x_1002);
lean_dec(x_999);
x_1003 = !lean_is_exclusive(x_1000);
if (x_1003 == 0)
{
lean_object* x_1004; uint8_t x_1005; 
x_1004 = lean_ctor_get(x_1000, 1);
lean_dec(x_1004);
x_1005 = !lean_is_exclusive(x_1001);
if (x_1005 == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; 
x_1006 = lean_ctor_get(x_1001, 0);
x_1007 = lean_ctor_get(x_1001, 1);
lean_dec(x_1007);
x_1008 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1002);
x_1009 = !lean_is_exclusive(x_1008);
if (x_1009 == 0)
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; 
x_1010 = lean_ctor_get(x_1008, 0);
x_1011 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1010);
x_1012 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
x_1013 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1014 = lean_array_push(x_1013, x_992);
x_1015 = lean_box(2);
x_1016 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1017 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1017, 0, x_1015);
lean_ctor_set(x_1017, 1, x_1016);
lean_ctor_set(x_1017, 2, x_1014);
x_1018 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1019 = lean_array_push(x_1018, x_1017);
x_1020 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1021 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1021, 0, x_1015);
lean_ctor_set(x_1021, 1, x_1020);
lean_ctor_set(x_1021, 2, x_1019);
x_1022 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1010);
x_1023 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1023, 0, x_1010);
lean_ctor_set(x_1023, 1, x_1022);
x_1024 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1010);
x_1025 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1025, 0, x_1010);
lean_ctor_set(x_1025, 1, x_1024);
lean_inc(x_14);
x_1026 = lean_array_push(x_1018, x_14);
x_1027 = !lean_is_exclusive(x_14);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; uint8_t x_1055; lean_object* x_1056; 
x_1028 = lean_ctor_get(x_14, 2);
lean_dec(x_1028);
x_1029 = lean_ctor_get(x_14, 1);
lean_dec(x_1029);
x_1030 = lean_ctor_get(x_14, 0);
lean_dec(x_1030);
lean_ctor_set(x_14, 2, x_1026);
lean_ctor_set(x_14, 1, x_1020);
lean_ctor_set(x_14, 0, x_1015);
x_1031 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1032 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1032, 0, x_1010);
lean_ctor_set(x_1032, 1, x_1031);
x_1033 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1034 = lean_array_push(x_1033, x_1025);
x_1035 = lean_array_push(x_1034, x_14);
x_1036 = lean_array_push(x_1035, x_1032);
x_1037 = lean_array_push(x_1036, x_1006);
x_1038 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1039 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1039, 0, x_1015);
lean_ctor_set(x_1039, 1, x_1038);
lean_ctor_set(x_1039, 2, x_1037);
x_1040 = lean_array_push(x_1018, x_1039);
x_1041 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1041, 0, x_1015);
lean_ctor_set(x_1041, 1, x_1020);
lean_ctor_set(x_1041, 2, x_1040);
x_1042 = lean_array_push(x_1018, x_1041);
x_1043 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1044 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1044, 0, x_1015);
lean_ctor_set(x_1044, 1, x_1043);
lean_ctor_set(x_1044, 2, x_1042);
x_1045 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1046 = lean_array_push(x_1045, x_1012);
x_1047 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1048 = lean_array_push(x_1046, x_1047);
x_1049 = lean_array_push(x_1048, x_1021);
x_1050 = lean_array_push(x_1049, x_1047);
x_1051 = lean_array_push(x_1050, x_1023);
x_1052 = lean_array_push(x_1051, x_1044);
x_1053 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1054 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1054, 0, x_1015);
lean_ctor_set(x_1054, 1, x_1053);
lean_ctor_set(x_1054, 2, x_1052);
x_1055 = 1;
x_1056 = lean_box(x_1055);
lean_ctor_set(x_1001, 1, x_1056);
lean_ctor_set(x_1001, 0, x_1054);
lean_ctor_set(x_1008, 0, x_1000);
return x_1008;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; lean_object* x_1083; 
lean_dec(x_14);
x_1057 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1057, 0, x_1015);
lean_ctor_set(x_1057, 1, x_1020);
lean_ctor_set(x_1057, 2, x_1026);
x_1058 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1059 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1059, 0, x_1010);
lean_ctor_set(x_1059, 1, x_1058);
x_1060 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1061 = lean_array_push(x_1060, x_1025);
x_1062 = lean_array_push(x_1061, x_1057);
x_1063 = lean_array_push(x_1062, x_1059);
x_1064 = lean_array_push(x_1063, x_1006);
x_1065 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1066 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1066, 0, x_1015);
lean_ctor_set(x_1066, 1, x_1065);
lean_ctor_set(x_1066, 2, x_1064);
x_1067 = lean_array_push(x_1018, x_1066);
x_1068 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1068, 0, x_1015);
lean_ctor_set(x_1068, 1, x_1020);
lean_ctor_set(x_1068, 2, x_1067);
x_1069 = lean_array_push(x_1018, x_1068);
x_1070 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1071 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1071, 0, x_1015);
lean_ctor_set(x_1071, 1, x_1070);
lean_ctor_set(x_1071, 2, x_1069);
x_1072 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1073 = lean_array_push(x_1072, x_1012);
x_1074 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1075 = lean_array_push(x_1073, x_1074);
x_1076 = lean_array_push(x_1075, x_1021);
x_1077 = lean_array_push(x_1076, x_1074);
x_1078 = lean_array_push(x_1077, x_1023);
x_1079 = lean_array_push(x_1078, x_1071);
x_1080 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1081 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1081, 0, x_1015);
lean_ctor_set(x_1081, 1, x_1080);
lean_ctor_set(x_1081, 2, x_1079);
x_1082 = 1;
x_1083 = lean_box(x_1082);
lean_ctor_set(x_1001, 1, x_1083);
lean_ctor_set(x_1001, 0, x_1081);
lean_ctor_set(x_1008, 0, x_1000);
return x_1008;
}
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1084 = lean_ctor_get(x_1008, 0);
x_1085 = lean_ctor_get(x_1008, 1);
lean_inc(x_1085);
lean_inc(x_1084);
lean_dec(x_1008);
x_1086 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1084);
x_1087 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1087, 0, x_1084);
lean_ctor_set(x_1087, 1, x_1086);
x_1088 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1089 = lean_array_push(x_1088, x_992);
x_1090 = lean_box(2);
x_1091 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1092 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
lean_ctor_set(x_1092, 2, x_1089);
x_1093 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1094 = lean_array_push(x_1093, x_1092);
x_1095 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1096 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1096, 0, x_1090);
lean_ctor_set(x_1096, 1, x_1095);
lean_ctor_set(x_1096, 2, x_1094);
x_1097 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1084);
x_1098 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1098, 0, x_1084);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1084);
x_1100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1100, 0, x_1084);
lean_ctor_set(x_1100, 1, x_1099);
lean_inc(x_14);
x_1101 = lean_array_push(x_1093, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1102 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1090);
lean_ctor_set(x_1103, 1, x_1095);
lean_ctor_set(x_1103, 2, x_1101);
x_1104 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1105, 0, x_1084);
lean_ctor_set(x_1105, 1, x_1104);
x_1106 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1107 = lean_array_push(x_1106, x_1100);
x_1108 = lean_array_push(x_1107, x_1103);
x_1109 = lean_array_push(x_1108, x_1105);
x_1110 = lean_array_push(x_1109, x_1006);
x_1111 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1112, 0, x_1090);
lean_ctor_set(x_1112, 1, x_1111);
lean_ctor_set(x_1112, 2, x_1110);
x_1113 = lean_array_push(x_1093, x_1112);
x_1114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1114, 0, x_1090);
lean_ctor_set(x_1114, 1, x_1095);
lean_ctor_set(x_1114, 2, x_1113);
x_1115 = lean_array_push(x_1093, x_1114);
x_1116 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1117, 0, x_1090);
lean_ctor_set(x_1117, 1, x_1116);
lean_ctor_set(x_1117, 2, x_1115);
x_1118 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1119 = lean_array_push(x_1118, x_1087);
x_1120 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1121 = lean_array_push(x_1119, x_1120);
x_1122 = lean_array_push(x_1121, x_1096);
x_1123 = lean_array_push(x_1122, x_1120);
x_1124 = lean_array_push(x_1123, x_1098);
x_1125 = lean_array_push(x_1124, x_1117);
x_1126 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1127, 0, x_1090);
lean_ctor_set(x_1127, 1, x_1126);
lean_ctor_set(x_1127, 2, x_1125);
x_1128 = 1;
x_1129 = lean_box(x_1128);
lean_ctor_set(x_1001, 1, x_1129);
lean_ctor_set(x_1001, 0, x_1127);
x_1130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1130, 0, x_1000);
lean_ctor_set(x_1130, 1, x_1085);
return x_1130;
}
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; uint8_t x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
x_1131 = lean_ctor_get(x_1001, 0);
lean_inc(x_1131);
lean_dec(x_1001);
x_1132 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1002);
x_1133 = lean_ctor_get(x_1132, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1132, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1132)) {
 lean_ctor_release(x_1132, 0);
 lean_ctor_release(x_1132, 1);
 x_1135 = x_1132;
} else {
 lean_dec_ref(x_1132);
 x_1135 = lean_box(0);
}
x_1136 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1133);
x_1137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1137, 0, x_1133);
lean_ctor_set(x_1137, 1, x_1136);
x_1138 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1139 = lean_array_push(x_1138, x_992);
x_1140 = lean_box(2);
x_1141 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1142, 0, x_1140);
lean_ctor_set(x_1142, 1, x_1141);
lean_ctor_set(x_1142, 2, x_1139);
x_1143 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1144 = lean_array_push(x_1143, x_1142);
x_1145 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1146, 0, x_1140);
lean_ctor_set(x_1146, 1, x_1145);
lean_ctor_set(x_1146, 2, x_1144);
x_1147 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1133);
x_1148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1148, 0, x_1133);
lean_ctor_set(x_1148, 1, x_1147);
x_1149 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1133);
x_1150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1150, 0, x_1133);
lean_ctor_set(x_1150, 1, x_1149);
lean_inc(x_14);
x_1151 = lean_array_push(x_1143, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1152 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1152 = lean_box(0);
}
if (lean_is_scalar(x_1152)) {
 x_1153 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1153 = x_1152;
}
lean_ctor_set(x_1153, 0, x_1140);
lean_ctor_set(x_1153, 1, x_1145);
lean_ctor_set(x_1153, 2, x_1151);
x_1154 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1155, 0, x_1133);
lean_ctor_set(x_1155, 1, x_1154);
x_1156 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1157 = lean_array_push(x_1156, x_1150);
x_1158 = lean_array_push(x_1157, x_1153);
x_1159 = lean_array_push(x_1158, x_1155);
x_1160 = lean_array_push(x_1159, x_1131);
x_1161 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1162, 0, x_1140);
lean_ctor_set(x_1162, 1, x_1161);
lean_ctor_set(x_1162, 2, x_1160);
x_1163 = lean_array_push(x_1143, x_1162);
x_1164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1164, 0, x_1140);
lean_ctor_set(x_1164, 1, x_1145);
lean_ctor_set(x_1164, 2, x_1163);
x_1165 = lean_array_push(x_1143, x_1164);
x_1166 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1167, 0, x_1140);
lean_ctor_set(x_1167, 1, x_1166);
lean_ctor_set(x_1167, 2, x_1165);
x_1168 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1169 = lean_array_push(x_1168, x_1137);
x_1170 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1171 = lean_array_push(x_1169, x_1170);
x_1172 = lean_array_push(x_1171, x_1146);
x_1173 = lean_array_push(x_1172, x_1170);
x_1174 = lean_array_push(x_1173, x_1148);
x_1175 = lean_array_push(x_1174, x_1167);
x_1176 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1177, 0, x_1140);
lean_ctor_set(x_1177, 1, x_1176);
lean_ctor_set(x_1177, 2, x_1175);
x_1178 = 1;
x_1179 = lean_box(x_1178);
x_1180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1180, 0, x_1177);
lean_ctor_set(x_1180, 1, x_1179);
lean_ctor_set(x_1000, 1, x_1180);
if (lean_is_scalar(x_1135)) {
 x_1181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1181 = x_1135;
}
lean_ctor_set(x_1181, 0, x_1000);
lean_ctor_set(x_1181, 1, x_1134);
return x_1181;
}
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1182 = lean_ctor_get(x_1000, 0);
lean_inc(x_1182);
lean_dec(x_1000);
x_1183 = lean_ctor_get(x_1001, 0);
lean_inc(x_1183);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 lean_ctor_release(x_1001, 1);
 x_1184 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1184 = lean_box(0);
}
x_1185 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1002);
x_1186 = lean_ctor_get(x_1185, 0);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1185, 1);
lean_inc(x_1187);
if (lean_is_exclusive(x_1185)) {
 lean_ctor_release(x_1185, 0);
 lean_ctor_release(x_1185, 1);
 x_1188 = x_1185;
} else {
 lean_dec_ref(x_1185);
 x_1188 = lean_box(0);
}
x_1189 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1186);
x_1190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1190, 0, x_1186);
lean_ctor_set(x_1190, 1, x_1189);
x_1191 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1192 = lean_array_push(x_1191, x_992);
x_1193 = lean_box(2);
x_1194 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1195, 0, x_1193);
lean_ctor_set(x_1195, 1, x_1194);
lean_ctor_set(x_1195, 2, x_1192);
x_1196 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1197 = lean_array_push(x_1196, x_1195);
x_1198 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1199, 0, x_1193);
lean_ctor_set(x_1199, 1, x_1198);
lean_ctor_set(x_1199, 2, x_1197);
x_1200 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1186);
x_1201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1201, 0, x_1186);
lean_ctor_set(x_1201, 1, x_1200);
x_1202 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1186);
x_1203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1203, 0, x_1186);
lean_ctor_set(x_1203, 1, x_1202);
lean_inc(x_14);
x_1204 = lean_array_push(x_1196, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1205 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1205 = lean_box(0);
}
if (lean_is_scalar(x_1205)) {
 x_1206 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1206 = x_1205;
}
lean_ctor_set(x_1206, 0, x_1193);
lean_ctor_set(x_1206, 1, x_1198);
lean_ctor_set(x_1206, 2, x_1204);
x_1207 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1208, 0, x_1186);
lean_ctor_set(x_1208, 1, x_1207);
x_1209 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1210 = lean_array_push(x_1209, x_1203);
x_1211 = lean_array_push(x_1210, x_1206);
x_1212 = lean_array_push(x_1211, x_1208);
x_1213 = lean_array_push(x_1212, x_1183);
x_1214 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1215, 0, x_1193);
lean_ctor_set(x_1215, 1, x_1214);
lean_ctor_set(x_1215, 2, x_1213);
x_1216 = lean_array_push(x_1196, x_1215);
x_1217 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1217, 0, x_1193);
lean_ctor_set(x_1217, 1, x_1198);
lean_ctor_set(x_1217, 2, x_1216);
x_1218 = lean_array_push(x_1196, x_1217);
x_1219 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1220, 0, x_1193);
lean_ctor_set(x_1220, 1, x_1219);
lean_ctor_set(x_1220, 2, x_1218);
x_1221 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1222 = lean_array_push(x_1221, x_1190);
x_1223 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1224 = lean_array_push(x_1222, x_1223);
x_1225 = lean_array_push(x_1224, x_1199);
x_1226 = lean_array_push(x_1225, x_1223);
x_1227 = lean_array_push(x_1226, x_1201);
x_1228 = lean_array_push(x_1227, x_1220);
x_1229 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1230, 0, x_1193);
lean_ctor_set(x_1230, 1, x_1229);
lean_ctor_set(x_1230, 2, x_1228);
x_1231 = 1;
x_1232 = lean_box(x_1231);
if (lean_is_scalar(x_1184)) {
 x_1233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1233 = x_1184;
}
lean_ctor_set(x_1233, 0, x_1230);
lean_ctor_set(x_1233, 1, x_1232);
x_1234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1234, 0, x_1182);
lean_ctor_set(x_1234, 1, x_1233);
if (lean_is_scalar(x_1188)) {
 x_1235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1235 = x_1188;
}
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1187);
return x_1235;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; uint8_t x_1238; 
x_1236 = lean_unsigned_to_nat(1u);
x_1237 = l_Lean_Syntax_getArg(x_14, x_1236);
x_1238 = l_Lean_Syntax_isNone(x_1237);
if (x_1238 == 0)
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; uint8_t x_1242; 
x_1239 = lean_unsigned_to_nat(0u);
x_1240 = l_Lean_Syntax_getArg(x_1237, x_1239);
x_1241 = l_Lean_Syntax_getArg(x_1237, x_1236);
lean_dec(x_1237);
x_1242 = l_Lean_Syntax_isNone(x_1241);
if (x_1242 == 0)
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; uint8_t x_1246; 
x_1243 = l_Lean_Syntax_getArg(x_1241, x_1239);
lean_dec(x_1241);
lean_inc(x_1243);
x_1244 = l_Lean_Syntax_getKind(x_1243);
x_1245 = l_Lean_Elab_Term_expandFunBinders_loop___closed__18;
x_1246 = lean_name_eq(x_1244, x_1245);
lean_dec(x_1244);
if (x_1246 == 0)
{
lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; uint8_t x_1258; 
lean_dec(x_1243);
lean_dec(x_1240);
lean_inc(x_5);
lean_inc(x_14);
x_1247 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_1248 = lean_ctor_get(x_1247, 0);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1247, 1);
lean_inc(x_1249);
lean_dec(x_1247);
x_1250 = lean_nat_add(x_3, x_1236);
lean_dec(x_3);
lean_inc(x_14);
x_1251 = l_Lean_mkHole(x_14);
lean_inc(x_1248);
x_1252 = l_Lean_Elab_Term_mkExplicitBinder(x_1248, x_1251);
x_1253 = lean_array_push(x_4, x_1252);
lean_inc(x_5);
x_1254 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1250, x_1253, x_5, x_1249);
x_1255 = lean_ctor_get(x_1254, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1255, 1);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_1254, 1);
lean_inc(x_1257);
lean_dec(x_1254);
x_1258 = !lean_is_exclusive(x_1255);
if (x_1258 == 0)
{
lean_object* x_1259; uint8_t x_1260; 
x_1259 = lean_ctor_get(x_1255, 1);
lean_dec(x_1259);
x_1260 = !lean_is_exclusive(x_1256);
if (x_1260 == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; uint8_t x_1264; 
x_1261 = lean_ctor_get(x_1256, 0);
x_1262 = lean_ctor_get(x_1256, 1);
lean_dec(x_1262);
x_1263 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1257);
x_1264 = !lean_is_exclusive(x_1263);
if (x_1264 == 0)
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
x_1265 = lean_ctor_get(x_1263, 0);
x_1266 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1265);
x_1267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1267, 0, x_1265);
lean_ctor_set(x_1267, 1, x_1266);
x_1268 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1269 = lean_array_push(x_1268, x_1248);
x_1270 = lean_box(2);
x_1271 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1272 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
lean_ctor_set(x_1272, 2, x_1269);
x_1273 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1274 = lean_array_push(x_1273, x_1272);
x_1275 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1276 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1276, 0, x_1270);
lean_ctor_set(x_1276, 1, x_1275);
lean_ctor_set(x_1276, 2, x_1274);
x_1277 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1265);
x_1278 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1278, 0, x_1265);
lean_ctor_set(x_1278, 1, x_1277);
x_1279 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1265);
x_1280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1280, 0, x_1265);
lean_ctor_set(x_1280, 1, x_1279);
lean_inc(x_14);
x_1281 = lean_array_push(x_1273, x_14);
x_1282 = !lean_is_exclusive(x_14);
if (x_1282 == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; lean_object* x_1311; 
x_1283 = lean_ctor_get(x_14, 2);
lean_dec(x_1283);
x_1284 = lean_ctor_get(x_14, 1);
lean_dec(x_1284);
x_1285 = lean_ctor_get(x_14, 0);
lean_dec(x_1285);
lean_ctor_set(x_14, 2, x_1281);
lean_ctor_set(x_14, 1, x_1275);
lean_ctor_set(x_14, 0, x_1270);
x_1286 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1287, 0, x_1265);
lean_ctor_set(x_1287, 1, x_1286);
x_1288 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1289 = lean_array_push(x_1288, x_1280);
x_1290 = lean_array_push(x_1289, x_14);
x_1291 = lean_array_push(x_1290, x_1287);
x_1292 = lean_array_push(x_1291, x_1261);
x_1293 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1294, 0, x_1270);
lean_ctor_set(x_1294, 1, x_1293);
lean_ctor_set(x_1294, 2, x_1292);
x_1295 = lean_array_push(x_1273, x_1294);
x_1296 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1296, 0, x_1270);
lean_ctor_set(x_1296, 1, x_1275);
lean_ctor_set(x_1296, 2, x_1295);
x_1297 = lean_array_push(x_1273, x_1296);
x_1298 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1299, 0, x_1270);
lean_ctor_set(x_1299, 1, x_1298);
lean_ctor_set(x_1299, 2, x_1297);
x_1300 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1301 = lean_array_push(x_1300, x_1267);
x_1302 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1303 = lean_array_push(x_1301, x_1302);
x_1304 = lean_array_push(x_1303, x_1276);
x_1305 = lean_array_push(x_1304, x_1302);
x_1306 = lean_array_push(x_1305, x_1278);
x_1307 = lean_array_push(x_1306, x_1299);
x_1308 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1309, 0, x_1270);
lean_ctor_set(x_1309, 1, x_1308);
lean_ctor_set(x_1309, 2, x_1307);
x_1310 = 1;
x_1311 = lean_box(x_1310);
lean_ctor_set(x_1256, 1, x_1311);
lean_ctor_set(x_1256, 0, x_1309);
lean_ctor_set(x_1263, 0, x_1255);
return x_1263;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; uint8_t x_1337; lean_object* x_1338; 
lean_dec(x_14);
x_1312 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1312, 0, x_1270);
lean_ctor_set(x_1312, 1, x_1275);
lean_ctor_set(x_1312, 2, x_1281);
x_1313 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1314, 0, x_1265);
lean_ctor_set(x_1314, 1, x_1313);
x_1315 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1316 = lean_array_push(x_1315, x_1280);
x_1317 = lean_array_push(x_1316, x_1312);
x_1318 = lean_array_push(x_1317, x_1314);
x_1319 = lean_array_push(x_1318, x_1261);
x_1320 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1321 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1321, 0, x_1270);
lean_ctor_set(x_1321, 1, x_1320);
lean_ctor_set(x_1321, 2, x_1319);
x_1322 = lean_array_push(x_1273, x_1321);
x_1323 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1323, 0, x_1270);
lean_ctor_set(x_1323, 1, x_1275);
lean_ctor_set(x_1323, 2, x_1322);
x_1324 = lean_array_push(x_1273, x_1323);
x_1325 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1326 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1326, 0, x_1270);
lean_ctor_set(x_1326, 1, x_1325);
lean_ctor_set(x_1326, 2, x_1324);
x_1327 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1328 = lean_array_push(x_1327, x_1267);
x_1329 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1330 = lean_array_push(x_1328, x_1329);
x_1331 = lean_array_push(x_1330, x_1276);
x_1332 = lean_array_push(x_1331, x_1329);
x_1333 = lean_array_push(x_1332, x_1278);
x_1334 = lean_array_push(x_1333, x_1326);
x_1335 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1336 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1336, 0, x_1270);
lean_ctor_set(x_1336, 1, x_1335);
lean_ctor_set(x_1336, 2, x_1334);
x_1337 = 1;
x_1338 = lean_box(x_1337);
lean_ctor_set(x_1256, 1, x_1338);
lean_ctor_set(x_1256, 0, x_1336);
lean_ctor_set(x_1263, 0, x_1255);
return x_1263;
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1339 = lean_ctor_get(x_1263, 0);
x_1340 = lean_ctor_get(x_1263, 1);
lean_inc(x_1340);
lean_inc(x_1339);
lean_dec(x_1263);
x_1341 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1339);
x_1342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1342, 0, x_1339);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1344 = lean_array_push(x_1343, x_1248);
x_1345 = lean_box(2);
x_1346 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1347, 0, x_1345);
lean_ctor_set(x_1347, 1, x_1346);
lean_ctor_set(x_1347, 2, x_1344);
x_1348 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1349 = lean_array_push(x_1348, x_1347);
x_1350 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1351 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1351, 0, x_1345);
lean_ctor_set(x_1351, 1, x_1350);
lean_ctor_set(x_1351, 2, x_1349);
x_1352 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1339);
x_1353 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1353, 0, x_1339);
lean_ctor_set(x_1353, 1, x_1352);
x_1354 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1339);
x_1355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1355, 0, x_1339);
lean_ctor_set(x_1355, 1, x_1354);
lean_inc(x_14);
x_1356 = lean_array_push(x_1348, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1357 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1357 = lean_box(0);
}
if (lean_is_scalar(x_1357)) {
 x_1358 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1358 = x_1357;
}
lean_ctor_set(x_1358, 0, x_1345);
lean_ctor_set(x_1358, 1, x_1350);
lean_ctor_set(x_1358, 2, x_1356);
x_1359 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1360, 0, x_1339);
lean_ctor_set(x_1360, 1, x_1359);
x_1361 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1362 = lean_array_push(x_1361, x_1355);
x_1363 = lean_array_push(x_1362, x_1358);
x_1364 = lean_array_push(x_1363, x_1360);
x_1365 = lean_array_push(x_1364, x_1261);
x_1366 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1367 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1367, 0, x_1345);
lean_ctor_set(x_1367, 1, x_1366);
lean_ctor_set(x_1367, 2, x_1365);
x_1368 = lean_array_push(x_1348, x_1367);
x_1369 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1369, 0, x_1345);
lean_ctor_set(x_1369, 1, x_1350);
lean_ctor_set(x_1369, 2, x_1368);
x_1370 = lean_array_push(x_1348, x_1369);
x_1371 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1372, 0, x_1345);
lean_ctor_set(x_1372, 1, x_1371);
lean_ctor_set(x_1372, 2, x_1370);
x_1373 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1374 = lean_array_push(x_1373, x_1342);
x_1375 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1376 = lean_array_push(x_1374, x_1375);
x_1377 = lean_array_push(x_1376, x_1351);
x_1378 = lean_array_push(x_1377, x_1375);
x_1379 = lean_array_push(x_1378, x_1353);
x_1380 = lean_array_push(x_1379, x_1372);
x_1381 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1382 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1382, 0, x_1345);
lean_ctor_set(x_1382, 1, x_1381);
lean_ctor_set(x_1382, 2, x_1380);
x_1383 = 1;
x_1384 = lean_box(x_1383);
lean_ctor_set(x_1256, 1, x_1384);
lean_ctor_set(x_1256, 0, x_1382);
x_1385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1385, 0, x_1255);
lean_ctor_set(x_1385, 1, x_1340);
return x_1385;
}
}
else
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; uint8_t x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1386 = lean_ctor_get(x_1256, 0);
lean_inc(x_1386);
lean_dec(x_1256);
x_1387 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1257);
x_1388 = lean_ctor_get(x_1387, 0);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1387, 1);
lean_inc(x_1389);
if (lean_is_exclusive(x_1387)) {
 lean_ctor_release(x_1387, 0);
 lean_ctor_release(x_1387, 1);
 x_1390 = x_1387;
} else {
 lean_dec_ref(x_1387);
 x_1390 = lean_box(0);
}
x_1391 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1388);
x_1392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1392, 0, x_1388);
lean_ctor_set(x_1392, 1, x_1391);
x_1393 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1394 = lean_array_push(x_1393, x_1248);
x_1395 = lean_box(2);
x_1396 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1397 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1397, 0, x_1395);
lean_ctor_set(x_1397, 1, x_1396);
lean_ctor_set(x_1397, 2, x_1394);
x_1398 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1399 = lean_array_push(x_1398, x_1397);
x_1400 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1401 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1401, 0, x_1395);
lean_ctor_set(x_1401, 1, x_1400);
lean_ctor_set(x_1401, 2, x_1399);
x_1402 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1388);
x_1403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1403, 0, x_1388);
lean_ctor_set(x_1403, 1, x_1402);
x_1404 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1388);
x_1405 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1405, 0, x_1388);
lean_ctor_set(x_1405, 1, x_1404);
lean_inc(x_14);
x_1406 = lean_array_push(x_1398, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1407 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1407 = lean_box(0);
}
if (lean_is_scalar(x_1407)) {
 x_1408 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1408 = x_1407;
}
lean_ctor_set(x_1408, 0, x_1395);
lean_ctor_set(x_1408, 1, x_1400);
lean_ctor_set(x_1408, 2, x_1406);
x_1409 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1410, 0, x_1388);
lean_ctor_set(x_1410, 1, x_1409);
x_1411 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1412 = lean_array_push(x_1411, x_1405);
x_1413 = lean_array_push(x_1412, x_1408);
x_1414 = lean_array_push(x_1413, x_1410);
x_1415 = lean_array_push(x_1414, x_1386);
x_1416 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1417 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1417, 0, x_1395);
lean_ctor_set(x_1417, 1, x_1416);
lean_ctor_set(x_1417, 2, x_1415);
x_1418 = lean_array_push(x_1398, x_1417);
x_1419 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1419, 0, x_1395);
lean_ctor_set(x_1419, 1, x_1400);
lean_ctor_set(x_1419, 2, x_1418);
x_1420 = lean_array_push(x_1398, x_1419);
x_1421 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1422 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1422, 0, x_1395);
lean_ctor_set(x_1422, 1, x_1421);
lean_ctor_set(x_1422, 2, x_1420);
x_1423 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1424 = lean_array_push(x_1423, x_1392);
x_1425 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1426 = lean_array_push(x_1424, x_1425);
x_1427 = lean_array_push(x_1426, x_1401);
x_1428 = lean_array_push(x_1427, x_1425);
x_1429 = lean_array_push(x_1428, x_1403);
x_1430 = lean_array_push(x_1429, x_1422);
x_1431 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1432 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1432, 0, x_1395);
lean_ctor_set(x_1432, 1, x_1431);
lean_ctor_set(x_1432, 2, x_1430);
x_1433 = 1;
x_1434 = lean_box(x_1433);
x_1435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1435, 0, x_1432);
lean_ctor_set(x_1435, 1, x_1434);
lean_ctor_set(x_1255, 1, x_1435);
if (lean_is_scalar(x_1390)) {
 x_1436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1436 = x_1390;
}
lean_ctor_set(x_1436, 0, x_1255);
lean_ctor_set(x_1436, 1, x_1389);
return x_1436;
}
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
x_1437 = lean_ctor_get(x_1255, 0);
lean_inc(x_1437);
lean_dec(x_1255);
x_1438 = lean_ctor_get(x_1256, 0);
lean_inc(x_1438);
if (lean_is_exclusive(x_1256)) {
 lean_ctor_release(x_1256, 0);
 lean_ctor_release(x_1256, 1);
 x_1439 = x_1256;
} else {
 lean_dec_ref(x_1256);
 x_1439 = lean_box(0);
}
x_1440 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1257);
x_1441 = lean_ctor_get(x_1440, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1440, 1);
lean_inc(x_1442);
if (lean_is_exclusive(x_1440)) {
 lean_ctor_release(x_1440, 0);
 lean_ctor_release(x_1440, 1);
 x_1443 = x_1440;
} else {
 lean_dec_ref(x_1440);
 x_1443 = lean_box(0);
}
x_1444 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1441);
x_1445 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1445, 0, x_1441);
lean_ctor_set(x_1445, 1, x_1444);
x_1446 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1447 = lean_array_push(x_1446, x_1248);
x_1448 = lean_box(2);
x_1449 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1450, 0, x_1448);
lean_ctor_set(x_1450, 1, x_1449);
lean_ctor_set(x_1450, 2, x_1447);
x_1451 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1452 = lean_array_push(x_1451, x_1450);
x_1453 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1454 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1454, 0, x_1448);
lean_ctor_set(x_1454, 1, x_1453);
lean_ctor_set(x_1454, 2, x_1452);
x_1455 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1441);
x_1456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1456, 0, x_1441);
lean_ctor_set(x_1456, 1, x_1455);
x_1457 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1441);
x_1458 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1458, 0, x_1441);
lean_ctor_set(x_1458, 1, x_1457);
lean_inc(x_14);
x_1459 = lean_array_push(x_1451, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1460 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1460 = lean_box(0);
}
if (lean_is_scalar(x_1460)) {
 x_1461 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1461 = x_1460;
}
lean_ctor_set(x_1461, 0, x_1448);
lean_ctor_set(x_1461, 1, x_1453);
lean_ctor_set(x_1461, 2, x_1459);
x_1462 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1463, 0, x_1441);
lean_ctor_set(x_1463, 1, x_1462);
x_1464 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1465 = lean_array_push(x_1464, x_1458);
x_1466 = lean_array_push(x_1465, x_1461);
x_1467 = lean_array_push(x_1466, x_1463);
x_1468 = lean_array_push(x_1467, x_1438);
x_1469 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1470 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1470, 0, x_1448);
lean_ctor_set(x_1470, 1, x_1469);
lean_ctor_set(x_1470, 2, x_1468);
x_1471 = lean_array_push(x_1451, x_1470);
x_1472 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1472, 0, x_1448);
lean_ctor_set(x_1472, 1, x_1453);
lean_ctor_set(x_1472, 2, x_1471);
x_1473 = lean_array_push(x_1451, x_1472);
x_1474 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1475 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1475, 0, x_1448);
lean_ctor_set(x_1475, 1, x_1474);
lean_ctor_set(x_1475, 2, x_1473);
x_1476 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1477 = lean_array_push(x_1476, x_1445);
x_1478 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1479 = lean_array_push(x_1477, x_1478);
x_1480 = lean_array_push(x_1479, x_1454);
x_1481 = lean_array_push(x_1480, x_1478);
x_1482 = lean_array_push(x_1481, x_1456);
x_1483 = lean_array_push(x_1482, x_1475);
x_1484 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1485 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1485, 0, x_1448);
lean_ctor_set(x_1485, 1, x_1484);
lean_ctor_set(x_1485, 2, x_1483);
x_1486 = 1;
x_1487 = lean_box(x_1486);
if (lean_is_scalar(x_1439)) {
 x_1488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1488 = x_1439;
}
lean_ctor_set(x_1488, 0, x_1485);
lean_ctor_set(x_1488, 1, x_1487);
x_1489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1489, 0, x_1437);
lean_ctor_set(x_1489, 1, x_1488);
if (lean_is_scalar(x_1443)) {
 x_1490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1490 = x_1443;
}
lean_ctor_set(x_1490, 0, x_1489);
lean_ctor_set(x_1490, 1, x_1442);
return x_1490;
}
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
x_1491 = l_Lean_Syntax_getArg(x_1243, x_1236);
lean_dec(x_1243);
lean_inc(x_5);
x_1492 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_1240, x_5, x_6);
x_1493 = lean_ctor_get(x_1492, 0);
lean_inc(x_1493);
if (lean_obj_tag(x_1493) == 0)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; 
lean_dec(x_1491);
x_1494 = lean_ctor_get(x_1492, 1);
lean_inc(x_1494);
lean_dec(x_1492);
lean_inc(x_5);
lean_inc(x_14);
x_1495 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_1494);
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1495, 1);
lean_inc(x_1497);
lean_dec(x_1495);
x_1498 = lean_nat_add(x_3, x_1236);
lean_dec(x_3);
lean_inc(x_14);
x_1499 = l_Lean_mkHole(x_14);
lean_inc(x_1496);
x_1500 = l_Lean_Elab_Term_mkExplicitBinder(x_1496, x_1499);
x_1501 = lean_array_push(x_4, x_1500);
lean_inc(x_5);
x_1502 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1498, x_1501, x_5, x_1497);
x_1503 = lean_ctor_get(x_1502, 0);
lean_inc(x_1503);
x_1504 = lean_ctor_get(x_1503, 1);
lean_inc(x_1504);
x_1505 = lean_ctor_get(x_1502, 1);
lean_inc(x_1505);
lean_dec(x_1502);
x_1506 = !lean_is_exclusive(x_1503);
if (x_1506 == 0)
{
lean_object* x_1507; uint8_t x_1508; 
x_1507 = lean_ctor_get(x_1503, 1);
lean_dec(x_1507);
x_1508 = !lean_is_exclusive(x_1504);
if (x_1508 == 0)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; uint8_t x_1512; 
x_1509 = lean_ctor_get(x_1504, 0);
x_1510 = lean_ctor_get(x_1504, 1);
lean_dec(x_1510);
x_1511 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1505);
x_1512 = !lean_is_exclusive(x_1511);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; uint8_t x_1530; 
x_1513 = lean_ctor_get(x_1511, 0);
x_1514 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1513);
x_1515 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1515, 0, x_1513);
lean_ctor_set(x_1515, 1, x_1514);
x_1516 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1517 = lean_array_push(x_1516, x_1496);
x_1518 = lean_box(2);
x_1519 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1520 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set(x_1520, 1, x_1519);
lean_ctor_set(x_1520, 2, x_1517);
x_1521 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1522 = lean_array_push(x_1521, x_1520);
x_1523 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1524 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1524, 0, x_1518);
lean_ctor_set(x_1524, 1, x_1523);
lean_ctor_set(x_1524, 2, x_1522);
x_1525 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1513);
x_1526 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1526, 0, x_1513);
lean_ctor_set(x_1526, 1, x_1525);
x_1527 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1513);
x_1528 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1528, 0, x_1513);
lean_ctor_set(x_1528, 1, x_1527);
lean_inc(x_14);
x_1529 = lean_array_push(x_1521, x_14);
x_1530 = !lean_is_exclusive(x_14);
if (x_1530 == 0)
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; uint8_t x_1558; lean_object* x_1559; 
x_1531 = lean_ctor_get(x_14, 2);
lean_dec(x_1531);
x_1532 = lean_ctor_get(x_14, 1);
lean_dec(x_1532);
x_1533 = lean_ctor_get(x_14, 0);
lean_dec(x_1533);
lean_ctor_set(x_14, 2, x_1529);
lean_ctor_set(x_14, 1, x_1523);
lean_ctor_set(x_14, 0, x_1518);
x_1534 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1535 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1535, 0, x_1513);
lean_ctor_set(x_1535, 1, x_1534);
x_1536 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1537 = lean_array_push(x_1536, x_1528);
x_1538 = lean_array_push(x_1537, x_14);
x_1539 = lean_array_push(x_1538, x_1535);
x_1540 = lean_array_push(x_1539, x_1509);
x_1541 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1542 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1542, 0, x_1518);
lean_ctor_set(x_1542, 1, x_1541);
lean_ctor_set(x_1542, 2, x_1540);
x_1543 = lean_array_push(x_1521, x_1542);
x_1544 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1544, 0, x_1518);
lean_ctor_set(x_1544, 1, x_1523);
lean_ctor_set(x_1544, 2, x_1543);
x_1545 = lean_array_push(x_1521, x_1544);
x_1546 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1547 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1547, 0, x_1518);
lean_ctor_set(x_1547, 1, x_1546);
lean_ctor_set(x_1547, 2, x_1545);
x_1548 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1549 = lean_array_push(x_1548, x_1515);
x_1550 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1551 = lean_array_push(x_1549, x_1550);
x_1552 = lean_array_push(x_1551, x_1524);
x_1553 = lean_array_push(x_1552, x_1550);
x_1554 = lean_array_push(x_1553, x_1526);
x_1555 = lean_array_push(x_1554, x_1547);
x_1556 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1557 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1557, 0, x_1518);
lean_ctor_set(x_1557, 1, x_1556);
lean_ctor_set(x_1557, 2, x_1555);
x_1558 = 1;
x_1559 = lean_box(x_1558);
lean_ctor_set(x_1504, 1, x_1559);
lean_ctor_set(x_1504, 0, x_1557);
lean_ctor_set(x_1511, 0, x_1503);
return x_1511;
}
else
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; uint8_t x_1585; lean_object* x_1586; 
lean_dec(x_14);
x_1560 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1560, 0, x_1518);
lean_ctor_set(x_1560, 1, x_1523);
lean_ctor_set(x_1560, 2, x_1529);
x_1561 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1562 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1562, 0, x_1513);
lean_ctor_set(x_1562, 1, x_1561);
x_1563 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1564 = lean_array_push(x_1563, x_1528);
x_1565 = lean_array_push(x_1564, x_1560);
x_1566 = lean_array_push(x_1565, x_1562);
x_1567 = lean_array_push(x_1566, x_1509);
x_1568 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1569 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1569, 0, x_1518);
lean_ctor_set(x_1569, 1, x_1568);
lean_ctor_set(x_1569, 2, x_1567);
x_1570 = lean_array_push(x_1521, x_1569);
x_1571 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1571, 0, x_1518);
lean_ctor_set(x_1571, 1, x_1523);
lean_ctor_set(x_1571, 2, x_1570);
x_1572 = lean_array_push(x_1521, x_1571);
x_1573 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1574 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1574, 0, x_1518);
lean_ctor_set(x_1574, 1, x_1573);
lean_ctor_set(x_1574, 2, x_1572);
x_1575 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1576 = lean_array_push(x_1575, x_1515);
x_1577 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1578 = lean_array_push(x_1576, x_1577);
x_1579 = lean_array_push(x_1578, x_1524);
x_1580 = lean_array_push(x_1579, x_1577);
x_1581 = lean_array_push(x_1580, x_1526);
x_1582 = lean_array_push(x_1581, x_1574);
x_1583 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1584 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1584, 0, x_1518);
lean_ctor_set(x_1584, 1, x_1583);
lean_ctor_set(x_1584, 2, x_1582);
x_1585 = 1;
x_1586 = lean_box(x_1585);
lean_ctor_set(x_1504, 1, x_1586);
lean_ctor_set(x_1504, 0, x_1584);
lean_ctor_set(x_1511, 0, x_1503);
return x_1511;
}
}
else
{
lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; uint8_t x_1631; lean_object* x_1632; lean_object* x_1633; 
x_1587 = lean_ctor_get(x_1511, 0);
x_1588 = lean_ctor_get(x_1511, 1);
lean_inc(x_1588);
lean_inc(x_1587);
lean_dec(x_1511);
x_1589 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1587);
x_1590 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1590, 0, x_1587);
lean_ctor_set(x_1590, 1, x_1589);
x_1591 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1592 = lean_array_push(x_1591, x_1496);
x_1593 = lean_box(2);
x_1594 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1595 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1595, 0, x_1593);
lean_ctor_set(x_1595, 1, x_1594);
lean_ctor_set(x_1595, 2, x_1592);
x_1596 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1597 = lean_array_push(x_1596, x_1595);
x_1598 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1599 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1599, 0, x_1593);
lean_ctor_set(x_1599, 1, x_1598);
lean_ctor_set(x_1599, 2, x_1597);
x_1600 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1587);
x_1601 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1601, 0, x_1587);
lean_ctor_set(x_1601, 1, x_1600);
x_1602 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1587);
x_1603 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1603, 0, x_1587);
lean_ctor_set(x_1603, 1, x_1602);
lean_inc(x_14);
x_1604 = lean_array_push(x_1596, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1605 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1605 = lean_box(0);
}
if (lean_is_scalar(x_1605)) {
 x_1606 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1606 = x_1605;
}
lean_ctor_set(x_1606, 0, x_1593);
lean_ctor_set(x_1606, 1, x_1598);
lean_ctor_set(x_1606, 2, x_1604);
x_1607 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1608 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1608, 0, x_1587);
lean_ctor_set(x_1608, 1, x_1607);
x_1609 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1610 = lean_array_push(x_1609, x_1603);
x_1611 = lean_array_push(x_1610, x_1606);
x_1612 = lean_array_push(x_1611, x_1608);
x_1613 = lean_array_push(x_1612, x_1509);
x_1614 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1615 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1615, 0, x_1593);
lean_ctor_set(x_1615, 1, x_1614);
lean_ctor_set(x_1615, 2, x_1613);
x_1616 = lean_array_push(x_1596, x_1615);
x_1617 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1617, 0, x_1593);
lean_ctor_set(x_1617, 1, x_1598);
lean_ctor_set(x_1617, 2, x_1616);
x_1618 = lean_array_push(x_1596, x_1617);
x_1619 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1620 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1620, 0, x_1593);
lean_ctor_set(x_1620, 1, x_1619);
lean_ctor_set(x_1620, 2, x_1618);
x_1621 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1622 = lean_array_push(x_1621, x_1590);
x_1623 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1624 = lean_array_push(x_1622, x_1623);
x_1625 = lean_array_push(x_1624, x_1599);
x_1626 = lean_array_push(x_1625, x_1623);
x_1627 = lean_array_push(x_1626, x_1601);
x_1628 = lean_array_push(x_1627, x_1620);
x_1629 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1630 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1630, 0, x_1593);
lean_ctor_set(x_1630, 1, x_1629);
lean_ctor_set(x_1630, 2, x_1628);
x_1631 = 1;
x_1632 = lean_box(x_1631);
lean_ctor_set(x_1504, 1, x_1632);
lean_ctor_set(x_1504, 0, x_1630);
x_1633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1633, 0, x_1503);
lean_ctor_set(x_1633, 1, x_1588);
return x_1633;
}
}
else
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; uint8_t x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
x_1634 = lean_ctor_get(x_1504, 0);
lean_inc(x_1634);
lean_dec(x_1504);
x_1635 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1505);
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1635, 1);
lean_inc(x_1637);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1638 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1638 = lean_box(0);
}
x_1639 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1636);
x_1640 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1640, 0, x_1636);
lean_ctor_set(x_1640, 1, x_1639);
x_1641 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1642 = lean_array_push(x_1641, x_1496);
x_1643 = lean_box(2);
x_1644 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1645 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1645, 0, x_1643);
lean_ctor_set(x_1645, 1, x_1644);
lean_ctor_set(x_1645, 2, x_1642);
x_1646 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1647 = lean_array_push(x_1646, x_1645);
x_1648 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1649 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1649, 0, x_1643);
lean_ctor_set(x_1649, 1, x_1648);
lean_ctor_set(x_1649, 2, x_1647);
x_1650 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1636);
x_1651 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1651, 0, x_1636);
lean_ctor_set(x_1651, 1, x_1650);
x_1652 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1636);
x_1653 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1653, 0, x_1636);
lean_ctor_set(x_1653, 1, x_1652);
lean_inc(x_14);
x_1654 = lean_array_push(x_1646, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1655 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1655 = lean_box(0);
}
if (lean_is_scalar(x_1655)) {
 x_1656 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1656 = x_1655;
}
lean_ctor_set(x_1656, 0, x_1643);
lean_ctor_set(x_1656, 1, x_1648);
lean_ctor_set(x_1656, 2, x_1654);
x_1657 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1658 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1658, 0, x_1636);
lean_ctor_set(x_1658, 1, x_1657);
x_1659 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1660 = lean_array_push(x_1659, x_1653);
x_1661 = lean_array_push(x_1660, x_1656);
x_1662 = lean_array_push(x_1661, x_1658);
x_1663 = lean_array_push(x_1662, x_1634);
x_1664 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1665 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1665, 0, x_1643);
lean_ctor_set(x_1665, 1, x_1664);
lean_ctor_set(x_1665, 2, x_1663);
x_1666 = lean_array_push(x_1646, x_1665);
x_1667 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1667, 0, x_1643);
lean_ctor_set(x_1667, 1, x_1648);
lean_ctor_set(x_1667, 2, x_1666);
x_1668 = lean_array_push(x_1646, x_1667);
x_1669 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1670 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1670, 0, x_1643);
lean_ctor_set(x_1670, 1, x_1669);
lean_ctor_set(x_1670, 2, x_1668);
x_1671 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1672 = lean_array_push(x_1671, x_1640);
x_1673 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1674 = lean_array_push(x_1672, x_1673);
x_1675 = lean_array_push(x_1674, x_1649);
x_1676 = lean_array_push(x_1675, x_1673);
x_1677 = lean_array_push(x_1676, x_1651);
x_1678 = lean_array_push(x_1677, x_1670);
x_1679 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1680 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1680, 0, x_1643);
lean_ctor_set(x_1680, 1, x_1679);
lean_ctor_set(x_1680, 2, x_1678);
x_1681 = 1;
x_1682 = lean_box(x_1681);
x_1683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1683, 0, x_1680);
lean_ctor_set(x_1683, 1, x_1682);
lean_ctor_set(x_1503, 1, x_1683);
if (lean_is_scalar(x_1638)) {
 x_1684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1684 = x_1638;
}
lean_ctor_set(x_1684, 0, x_1503);
lean_ctor_set(x_1684, 1, x_1637);
return x_1684;
}
}
else
{
lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; uint8_t x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; 
x_1685 = lean_ctor_get(x_1503, 0);
lean_inc(x_1685);
lean_dec(x_1503);
x_1686 = lean_ctor_get(x_1504, 0);
lean_inc(x_1686);
if (lean_is_exclusive(x_1504)) {
 lean_ctor_release(x_1504, 0);
 lean_ctor_release(x_1504, 1);
 x_1687 = x_1504;
} else {
 lean_dec_ref(x_1504);
 x_1687 = lean_box(0);
}
x_1688 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1505);
x_1689 = lean_ctor_get(x_1688, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1688, 1);
lean_inc(x_1690);
if (lean_is_exclusive(x_1688)) {
 lean_ctor_release(x_1688, 0);
 lean_ctor_release(x_1688, 1);
 x_1691 = x_1688;
} else {
 lean_dec_ref(x_1688);
 x_1691 = lean_box(0);
}
x_1692 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1689);
x_1693 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1693, 0, x_1689);
lean_ctor_set(x_1693, 1, x_1692);
x_1694 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1695 = lean_array_push(x_1694, x_1496);
x_1696 = lean_box(2);
x_1697 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1698 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1698, 0, x_1696);
lean_ctor_set(x_1698, 1, x_1697);
lean_ctor_set(x_1698, 2, x_1695);
x_1699 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1700 = lean_array_push(x_1699, x_1698);
x_1701 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1702 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1702, 0, x_1696);
lean_ctor_set(x_1702, 1, x_1701);
lean_ctor_set(x_1702, 2, x_1700);
x_1703 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1689);
x_1704 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1704, 0, x_1689);
lean_ctor_set(x_1704, 1, x_1703);
x_1705 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1689);
x_1706 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1706, 0, x_1689);
lean_ctor_set(x_1706, 1, x_1705);
lean_inc(x_14);
x_1707 = lean_array_push(x_1699, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1708 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1708 = lean_box(0);
}
if (lean_is_scalar(x_1708)) {
 x_1709 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1709 = x_1708;
}
lean_ctor_set(x_1709, 0, x_1696);
lean_ctor_set(x_1709, 1, x_1701);
lean_ctor_set(x_1709, 2, x_1707);
x_1710 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1711 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1711, 0, x_1689);
lean_ctor_set(x_1711, 1, x_1710);
x_1712 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1713 = lean_array_push(x_1712, x_1706);
x_1714 = lean_array_push(x_1713, x_1709);
x_1715 = lean_array_push(x_1714, x_1711);
x_1716 = lean_array_push(x_1715, x_1686);
x_1717 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1718 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1718, 0, x_1696);
lean_ctor_set(x_1718, 1, x_1717);
lean_ctor_set(x_1718, 2, x_1716);
x_1719 = lean_array_push(x_1699, x_1718);
x_1720 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1720, 0, x_1696);
lean_ctor_set(x_1720, 1, x_1701);
lean_ctor_set(x_1720, 2, x_1719);
x_1721 = lean_array_push(x_1699, x_1720);
x_1722 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1723 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1723, 0, x_1696);
lean_ctor_set(x_1723, 1, x_1722);
lean_ctor_set(x_1723, 2, x_1721);
x_1724 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1725 = lean_array_push(x_1724, x_1693);
x_1726 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1727 = lean_array_push(x_1725, x_1726);
x_1728 = lean_array_push(x_1727, x_1702);
x_1729 = lean_array_push(x_1728, x_1726);
x_1730 = lean_array_push(x_1729, x_1704);
x_1731 = lean_array_push(x_1730, x_1723);
x_1732 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1733 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1733, 0, x_1696);
lean_ctor_set(x_1733, 1, x_1732);
lean_ctor_set(x_1733, 2, x_1731);
x_1734 = 1;
x_1735 = lean_box(x_1734);
if (lean_is_scalar(x_1687)) {
 x_1736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1736 = x_1687;
}
lean_ctor_set(x_1736, 0, x_1733);
lean_ctor_set(x_1736, 1, x_1735);
x_1737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1737, 0, x_1685);
lean_ctor_set(x_1737, 1, x_1736);
if (lean_is_scalar(x_1691)) {
 x_1738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1738 = x_1691;
}
lean_ctor_set(x_1738, 0, x_1737);
lean_ctor_set(x_1738, 1, x_1690);
return x_1738;
}
}
else
{
lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; size_t x_1743; size_t x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; 
lean_dec(x_14);
x_1739 = lean_ctor_get(x_1492, 1);
lean_inc(x_1739);
lean_dec(x_1492);
x_1740 = lean_ctor_get(x_1493, 0);
lean_inc(x_1740);
lean_dec(x_1493);
x_1741 = lean_nat_add(x_3, x_1236);
lean_dec(x_3);
x_1742 = lean_array_get_size(x_1740);
x_1743 = lean_usize_of_nat(x_1742);
lean_dec(x_1742);
x_1744 = 0;
x_1745 = x_1740;
x_1746 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3(x_1491, x_1743, x_1744, x_1745);
x_1747 = x_1746;
x_1748 = l_Array_append___rarg(x_4, x_1747);
x_3 = x_1741;
x_4 = x_1748;
x_6 = x_1739;
goto _start;
}
}
}
else
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; uint8_t x_1761; 
lean_dec(x_1241);
lean_dec(x_1240);
lean_inc(x_5);
lean_inc(x_14);
x_1750 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_1751 = lean_ctor_get(x_1750, 0);
lean_inc(x_1751);
x_1752 = lean_ctor_get(x_1750, 1);
lean_inc(x_1752);
lean_dec(x_1750);
x_1753 = lean_nat_add(x_3, x_1236);
lean_dec(x_3);
lean_inc(x_14);
x_1754 = l_Lean_mkHole(x_14);
lean_inc(x_1751);
x_1755 = l_Lean_Elab_Term_mkExplicitBinder(x_1751, x_1754);
x_1756 = lean_array_push(x_4, x_1755);
lean_inc(x_5);
x_1757 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1753, x_1756, x_5, x_1752);
x_1758 = lean_ctor_get(x_1757, 0);
lean_inc(x_1758);
x_1759 = lean_ctor_get(x_1758, 1);
lean_inc(x_1759);
x_1760 = lean_ctor_get(x_1757, 1);
lean_inc(x_1760);
lean_dec(x_1757);
x_1761 = !lean_is_exclusive(x_1758);
if (x_1761 == 0)
{
lean_object* x_1762; uint8_t x_1763; 
x_1762 = lean_ctor_get(x_1758, 1);
lean_dec(x_1762);
x_1763 = !lean_is_exclusive(x_1759);
if (x_1763 == 0)
{
lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; uint8_t x_1767; 
x_1764 = lean_ctor_get(x_1759, 0);
x_1765 = lean_ctor_get(x_1759, 1);
lean_dec(x_1765);
x_1766 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1760);
x_1767 = !lean_is_exclusive(x_1766);
if (x_1767 == 0)
{
lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; uint8_t x_1785; 
x_1768 = lean_ctor_get(x_1766, 0);
x_1769 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1768);
x_1770 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1770, 0, x_1768);
lean_ctor_set(x_1770, 1, x_1769);
x_1771 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1772 = lean_array_push(x_1771, x_1751);
x_1773 = lean_box(2);
x_1774 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1775 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1775, 0, x_1773);
lean_ctor_set(x_1775, 1, x_1774);
lean_ctor_set(x_1775, 2, x_1772);
x_1776 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1777 = lean_array_push(x_1776, x_1775);
x_1778 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1779 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1779, 0, x_1773);
lean_ctor_set(x_1779, 1, x_1778);
lean_ctor_set(x_1779, 2, x_1777);
x_1780 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1768);
x_1781 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1781, 0, x_1768);
lean_ctor_set(x_1781, 1, x_1780);
x_1782 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1768);
x_1783 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1783, 0, x_1768);
lean_ctor_set(x_1783, 1, x_1782);
lean_inc(x_14);
x_1784 = lean_array_push(x_1776, x_14);
x_1785 = !lean_is_exclusive(x_14);
if (x_1785 == 0)
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; uint8_t x_1813; lean_object* x_1814; 
x_1786 = lean_ctor_get(x_14, 2);
lean_dec(x_1786);
x_1787 = lean_ctor_get(x_14, 1);
lean_dec(x_1787);
x_1788 = lean_ctor_get(x_14, 0);
lean_dec(x_1788);
lean_ctor_set(x_14, 2, x_1784);
lean_ctor_set(x_14, 1, x_1778);
lean_ctor_set(x_14, 0, x_1773);
x_1789 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1790 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1790, 0, x_1768);
lean_ctor_set(x_1790, 1, x_1789);
x_1791 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1792 = lean_array_push(x_1791, x_1783);
x_1793 = lean_array_push(x_1792, x_14);
x_1794 = lean_array_push(x_1793, x_1790);
x_1795 = lean_array_push(x_1794, x_1764);
x_1796 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1797 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1797, 0, x_1773);
lean_ctor_set(x_1797, 1, x_1796);
lean_ctor_set(x_1797, 2, x_1795);
x_1798 = lean_array_push(x_1776, x_1797);
x_1799 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1799, 0, x_1773);
lean_ctor_set(x_1799, 1, x_1778);
lean_ctor_set(x_1799, 2, x_1798);
x_1800 = lean_array_push(x_1776, x_1799);
x_1801 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1802 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1802, 0, x_1773);
lean_ctor_set(x_1802, 1, x_1801);
lean_ctor_set(x_1802, 2, x_1800);
x_1803 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1804 = lean_array_push(x_1803, x_1770);
x_1805 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1806 = lean_array_push(x_1804, x_1805);
x_1807 = lean_array_push(x_1806, x_1779);
x_1808 = lean_array_push(x_1807, x_1805);
x_1809 = lean_array_push(x_1808, x_1781);
x_1810 = lean_array_push(x_1809, x_1802);
x_1811 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1812 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1812, 0, x_1773);
lean_ctor_set(x_1812, 1, x_1811);
lean_ctor_set(x_1812, 2, x_1810);
x_1813 = 1;
x_1814 = lean_box(x_1813);
lean_ctor_set(x_1759, 1, x_1814);
lean_ctor_set(x_1759, 0, x_1812);
lean_ctor_set(x_1766, 0, x_1758);
return x_1766;
}
else
{
lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; uint8_t x_1840; lean_object* x_1841; 
lean_dec(x_14);
x_1815 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1815, 0, x_1773);
lean_ctor_set(x_1815, 1, x_1778);
lean_ctor_set(x_1815, 2, x_1784);
x_1816 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1817 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1817, 0, x_1768);
lean_ctor_set(x_1817, 1, x_1816);
x_1818 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1819 = lean_array_push(x_1818, x_1783);
x_1820 = lean_array_push(x_1819, x_1815);
x_1821 = lean_array_push(x_1820, x_1817);
x_1822 = lean_array_push(x_1821, x_1764);
x_1823 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1824 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1824, 0, x_1773);
lean_ctor_set(x_1824, 1, x_1823);
lean_ctor_set(x_1824, 2, x_1822);
x_1825 = lean_array_push(x_1776, x_1824);
x_1826 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1826, 0, x_1773);
lean_ctor_set(x_1826, 1, x_1778);
lean_ctor_set(x_1826, 2, x_1825);
x_1827 = lean_array_push(x_1776, x_1826);
x_1828 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1829 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1829, 0, x_1773);
lean_ctor_set(x_1829, 1, x_1828);
lean_ctor_set(x_1829, 2, x_1827);
x_1830 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1831 = lean_array_push(x_1830, x_1770);
x_1832 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1833 = lean_array_push(x_1831, x_1832);
x_1834 = lean_array_push(x_1833, x_1779);
x_1835 = lean_array_push(x_1834, x_1832);
x_1836 = lean_array_push(x_1835, x_1781);
x_1837 = lean_array_push(x_1836, x_1829);
x_1838 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1839 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1839, 0, x_1773);
lean_ctor_set(x_1839, 1, x_1838);
lean_ctor_set(x_1839, 2, x_1837);
x_1840 = 1;
x_1841 = lean_box(x_1840);
lean_ctor_set(x_1759, 1, x_1841);
lean_ctor_set(x_1759, 0, x_1839);
lean_ctor_set(x_1766, 0, x_1758);
return x_1766;
}
}
else
{
lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; uint8_t x_1886; lean_object* x_1887; lean_object* x_1888; 
x_1842 = lean_ctor_get(x_1766, 0);
x_1843 = lean_ctor_get(x_1766, 1);
lean_inc(x_1843);
lean_inc(x_1842);
lean_dec(x_1766);
x_1844 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1842);
x_1845 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1845, 0, x_1842);
lean_ctor_set(x_1845, 1, x_1844);
x_1846 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1847 = lean_array_push(x_1846, x_1751);
x_1848 = lean_box(2);
x_1849 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1850 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1850, 0, x_1848);
lean_ctor_set(x_1850, 1, x_1849);
lean_ctor_set(x_1850, 2, x_1847);
x_1851 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1852 = lean_array_push(x_1851, x_1850);
x_1853 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1854 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1854, 0, x_1848);
lean_ctor_set(x_1854, 1, x_1853);
lean_ctor_set(x_1854, 2, x_1852);
x_1855 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1842);
x_1856 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1856, 0, x_1842);
lean_ctor_set(x_1856, 1, x_1855);
x_1857 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1842);
x_1858 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1858, 0, x_1842);
lean_ctor_set(x_1858, 1, x_1857);
lean_inc(x_14);
x_1859 = lean_array_push(x_1851, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1860 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1860 = lean_box(0);
}
if (lean_is_scalar(x_1860)) {
 x_1861 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1861 = x_1860;
}
lean_ctor_set(x_1861, 0, x_1848);
lean_ctor_set(x_1861, 1, x_1853);
lean_ctor_set(x_1861, 2, x_1859);
x_1862 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1863 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1863, 0, x_1842);
lean_ctor_set(x_1863, 1, x_1862);
x_1864 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1865 = lean_array_push(x_1864, x_1858);
x_1866 = lean_array_push(x_1865, x_1861);
x_1867 = lean_array_push(x_1866, x_1863);
x_1868 = lean_array_push(x_1867, x_1764);
x_1869 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1870 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1870, 0, x_1848);
lean_ctor_set(x_1870, 1, x_1869);
lean_ctor_set(x_1870, 2, x_1868);
x_1871 = lean_array_push(x_1851, x_1870);
x_1872 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1872, 0, x_1848);
lean_ctor_set(x_1872, 1, x_1853);
lean_ctor_set(x_1872, 2, x_1871);
x_1873 = lean_array_push(x_1851, x_1872);
x_1874 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1875 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1875, 0, x_1848);
lean_ctor_set(x_1875, 1, x_1874);
lean_ctor_set(x_1875, 2, x_1873);
x_1876 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1877 = lean_array_push(x_1876, x_1845);
x_1878 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1879 = lean_array_push(x_1877, x_1878);
x_1880 = lean_array_push(x_1879, x_1854);
x_1881 = lean_array_push(x_1880, x_1878);
x_1882 = lean_array_push(x_1881, x_1856);
x_1883 = lean_array_push(x_1882, x_1875);
x_1884 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1885 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1885, 0, x_1848);
lean_ctor_set(x_1885, 1, x_1884);
lean_ctor_set(x_1885, 2, x_1883);
x_1886 = 1;
x_1887 = lean_box(x_1886);
lean_ctor_set(x_1759, 1, x_1887);
lean_ctor_set(x_1759, 0, x_1885);
x_1888 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1888, 0, x_1758);
lean_ctor_set(x_1888, 1, x_1843);
return x_1888;
}
}
else
{
lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; uint8_t x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; 
x_1889 = lean_ctor_get(x_1759, 0);
lean_inc(x_1889);
lean_dec(x_1759);
x_1890 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1760);
x_1891 = lean_ctor_get(x_1890, 0);
lean_inc(x_1891);
x_1892 = lean_ctor_get(x_1890, 1);
lean_inc(x_1892);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 x_1893 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_1893 = lean_box(0);
}
x_1894 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1891);
x_1895 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1895, 0, x_1891);
lean_ctor_set(x_1895, 1, x_1894);
x_1896 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1897 = lean_array_push(x_1896, x_1751);
x_1898 = lean_box(2);
x_1899 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1900 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1900, 0, x_1898);
lean_ctor_set(x_1900, 1, x_1899);
lean_ctor_set(x_1900, 2, x_1897);
x_1901 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1902 = lean_array_push(x_1901, x_1900);
x_1903 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1904 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1904, 0, x_1898);
lean_ctor_set(x_1904, 1, x_1903);
lean_ctor_set(x_1904, 2, x_1902);
x_1905 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1891);
x_1906 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1906, 0, x_1891);
lean_ctor_set(x_1906, 1, x_1905);
x_1907 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1891);
x_1908 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1908, 0, x_1891);
lean_ctor_set(x_1908, 1, x_1907);
lean_inc(x_14);
x_1909 = lean_array_push(x_1901, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1910 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1910 = lean_box(0);
}
if (lean_is_scalar(x_1910)) {
 x_1911 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1911 = x_1910;
}
lean_ctor_set(x_1911, 0, x_1898);
lean_ctor_set(x_1911, 1, x_1903);
lean_ctor_set(x_1911, 2, x_1909);
x_1912 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1913 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1913, 0, x_1891);
lean_ctor_set(x_1913, 1, x_1912);
x_1914 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1915 = lean_array_push(x_1914, x_1908);
x_1916 = lean_array_push(x_1915, x_1911);
x_1917 = lean_array_push(x_1916, x_1913);
x_1918 = lean_array_push(x_1917, x_1889);
x_1919 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1920 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1920, 0, x_1898);
lean_ctor_set(x_1920, 1, x_1919);
lean_ctor_set(x_1920, 2, x_1918);
x_1921 = lean_array_push(x_1901, x_1920);
x_1922 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1922, 0, x_1898);
lean_ctor_set(x_1922, 1, x_1903);
lean_ctor_set(x_1922, 2, x_1921);
x_1923 = lean_array_push(x_1901, x_1922);
x_1924 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1925 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1925, 0, x_1898);
lean_ctor_set(x_1925, 1, x_1924);
lean_ctor_set(x_1925, 2, x_1923);
x_1926 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1927 = lean_array_push(x_1926, x_1895);
x_1928 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1929 = lean_array_push(x_1927, x_1928);
x_1930 = lean_array_push(x_1929, x_1904);
x_1931 = lean_array_push(x_1930, x_1928);
x_1932 = lean_array_push(x_1931, x_1906);
x_1933 = lean_array_push(x_1932, x_1925);
x_1934 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1935 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1935, 0, x_1898);
lean_ctor_set(x_1935, 1, x_1934);
lean_ctor_set(x_1935, 2, x_1933);
x_1936 = 1;
x_1937 = lean_box(x_1936);
x_1938 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1938, 0, x_1935);
lean_ctor_set(x_1938, 1, x_1937);
lean_ctor_set(x_1758, 1, x_1938);
if (lean_is_scalar(x_1893)) {
 x_1939 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1939 = x_1893;
}
lean_ctor_set(x_1939, 0, x_1758);
lean_ctor_set(x_1939, 1, x_1892);
return x_1939;
}
}
else
{
lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; uint8_t x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; 
x_1940 = lean_ctor_get(x_1758, 0);
lean_inc(x_1940);
lean_dec(x_1758);
x_1941 = lean_ctor_get(x_1759, 0);
lean_inc(x_1941);
if (lean_is_exclusive(x_1759)) {
 lean_ctor_release(x_1759, 0);
 lean_ctor_release(x_1759, 1);
 x_1942 = x_1759;
} else {
 lean_dec_ref(x_1759);
 x_1942 = lean_box(0);
}
x_1943 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_1760);
x_1944 = lean_ctor_get(x_1943, 0);
lean_inc(x_1944);
x_1945 = lean_ctor_get(x_1943, 1);
lean_inc(x_1945);
if (lean_is_exclusive(x_1943)) {
 lean_ctor_release(x_1943, 0);
 lean_ctor_release(x_1943, 1);
 x_1946 = x_1943;
} else {
 lean_dec_ref(x_1943);
 x_1946 = lean_box(0);
}
x_1947 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_1944);
x_1948 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1948, 0, x_1944);
lean_ctor_set(x_1948, 1, x_1947);
x_1949 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_1950 = lean_array_push(x_1949, x_1751);
x_1951 = lean_box(2);
x_1952 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_1953 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1953, 0, x_1951);
lean_ctor_set(x_1953, 1, x_1952);
lean_ctor_set(x_1953, 2, x_1950);
x_1954 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_1955 = lean_array_push(x_1954, x_1953);
x_1956 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_1957 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1957, 0, x_1951);
lean_ctor_set(x_1957, 1, x_1956);
lean_ctor_set(x_1957, 2, x_1955);
x_1958 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_1944);
x_1959 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1959, 0, x_1944);
lean_ctor_set(x_1959, 1, x_1958);
x_1960 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_1944);
x_1961 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1961, 0, x_1944);
lean_ctor_set(x_1961, 1, x_1960);
lean_inc(x_14);
x_1962 = lean_array_push(x_1954, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_1963 = x_14;
} else {
 lean_dec_ref(x_14);
 x_1963 = lean_box(0);
}
if (lean_is_scalar(x_1963)) {
 x_1964 = lean_alloc_ctor(1, 3, 0);
} else {
 x_1964 = x_1963;
}
lean_ctor_set(x_1964, 0, x_1951);
lean_ctor_set(x_1964, 1, x_1956);
lean_ctor_set(x_1964, 2, x_1962);
x_1965 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_1966 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1966, 0, x_1944);
lean_ctor_set(x_1966, 1, x_1965);
x_1967 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_1968 = lean_array_push(x_1967, x_1961);
x_1969 = lean_array_push(x_1968, x_1964);
x_1970 = lean_array_push(x_1969, x_1966);
x_1971 = lean_array_push(x_1970, x_1941);
x_1972 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_1973 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1973, 0, x_1951);
lean_ctor_set(x_1973, 1, x_1972);
lean_ctor_set(x_1973, 2, x_1971);
x_1974 = lean_array_push(x_1954, x_1973);
x_1975 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1975, 0, x_1951);
lean_ctor_set(x_1975, 1, x_1956);
lean_ctor_set(x_1975, 2, x_1974);
x_1976 = lean_array_push(x_1954, x_1975);
x_1977 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_1978 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1978, 0, x_1951);
lean_ctor_set(x_1978, 1, x_1977);
lean_ctor_set(x_1978, 2, x_1976);
x_1979 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_1980 = lean_array_push(x_1979, x_1948);
x_1981 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_1982 = lean_array_push(x_1980, x_1981);
x_1983 = lean_array_push(x_1982, x_1957);
x_1984 = lean_array_push(x_1983, x_1981);
x_1985 = lean_array_push(x_1984, x_1959);
x_1986 = lean_array_push(x_1985, x_1978);
x_1987 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_1988 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1988, 0, x_1951);
lean_ctor_set(x_1988, 1, x_1987);
lean_ctor_set(x_1988, 2, x_1986);
x_1989 = 1;
x_1990 = lean_box(x_1989);
if (lean_is_scalar(x_1942)) {
 x_1991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1991 = x_1942;
}
lean_ctor_set(x_1991, 0, x_1988);
lean_ctor_set(x_1991, 1, x_1990);
x_1992 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1992, 0, x_1940);
lean_ctor_set(x_1992, 1, x_1991);
if (lean_is_scalar(x_1946)) {
 x_1993 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1993 = x_1946;
}
lean_ctor_set(x_1993, 0, x_1992);
lean_ctor_set(x_1993, 1, x_1945);
return x_1993;
}
}
}
else
{
lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; uint8_t x_2005; 
lean_dec(x_1237);
lean_inc(x_5);
lean_inc(x_14);
x_1994 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_1995 = lean_ctor_get(x_1994, 0);
lean_inc(x_1995);
x_1996 = lean_ctor_get(x_1994, 1);
lean_inc(x_1996);
lean_dec(x_1994);
x_1997 = lean_nat_add(x_3, x_1236);
lean_dec(x_3);
lean_inc(x_14);
x_1998 = l_Lean_mkHole(x_14);
lean_inc(x_1995);
x_1999 = l_Lean_Elab_Term_mkExplicitBinder(x_1995, x_1998);
x_2000 = lean_array_push(x_4, x_1999);
lean_inc(x_5);
x_2001 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_1997, x_2000, x_5, x_1996);
x_2002 = lean_ctor_get(x_2001, 0);
lean_inc(x_2002);
x_2003 = lean_ctor_get(x_2002, 1);
lean_inc(x_2003);
x_2004 = lean_ctor_get(x_2001, 1);
lean_inc(x_2004);
lean_dec(x_2001);
x_2005 = !lean_is_exclusive(x_2002);
if (x_2005 == 0)
{
lean_object* x_2006; uint8_t x_2007; 
x_2006 = lean_ctor_get(x_2002, 1);
lean_dec(x_2006);
x_2007 = !lean_is_exclusive(x_2003);
if (x_2007 == 0)
{
lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; uint8_t x_2011; 
x_2008 = lean_ctor_get(x_2003, 0);
x_2009 = lean_ctor_get(x_2003, 1);
lean_dec(x_2009);
x_2010 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2004);
x_2011 = !lean_is_exclusive(x_2010);
if (x_2011 == 0)
{
lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; uint8_t x_2029; 
x_2012 = lean_ctor_get(x_2010, 0);
x_2013 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2012);
x_2014 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2014, 0, x_2012);
lean_ctor_set(x_2014, 1, x_2013);
x_2015 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2016 = lean_array_push(x_2015, x_1995);
x_2017 = lean_box(2);
x_2018 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2019 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2019, 0, x_2017);
lean_ctor_set(x_2019, 1, x_2018);
lean_ctor_set(x_2019, 2, x_2016);
x_2020 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2021 = lean_array_push(x_2020, x_2019);
x_2022 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2023 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2023, 0, x_2017);
lean_ctor_set(x_2023, 1, x_2022);
lean_ctor_set(x_2023, 2, x_2021);
x_2024 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2012);
x_2025 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2025, 0, x_2012);
lean_ctor_set(x_2025, 1, x_2024);
x_2026 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2012);
x_2027 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2027, 0, x_2012);
lean_ctor_set(x_2027, 1, x_2026);
lean_inc(x_14);
x_2028 = lean_array_push(x_2020, x_14);
x_2029 = !lean_is_exclusive(x_14);
if (x_2029 == 0)
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; uint8_t x_2057; lean_object* x_2058; 
x_2030 = lean_ctor_get(x_14, 2);
lean_dec(x_2030);
x_2031 = lean_ctor_get(x_14, 1);
lean_dec(x_2031);
x_2032 = lean_ctor_get(x_14, 0);
lean_dec(x_2032);
lean_ctor_set(x_14, 2, x_2028);
lean_ctor_set(x_14, 1, x_2022);
lean_ctor_set(x_14, 0, x_2017);
x_2033 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2034 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2034, 0, x_2012);
lean_ctor_set(x_2034, 1, x_2033);
x_2035 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2036 = lean_array_push(x_2035, x_2027);
x_2037 = lean_array_push(x_2036, x_14);
x_2038 = lean_array_push(x_2037, x_2034);
x_2039 = lean_array_push(x_2038, x_2008);
x_2040 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2041 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2041, 0, x_2017);
lean_ctor_set(x_2041, 1, x_2040);
lean_ctor_set(x_2041, 2, x_2039);
x_2042 = lean_array_push(x_2020, x_2041);
x_2043 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2043, 0, x_2017);
lean_ctor_set(x_2043, 1, x_2022);
lean_ctor_set(x_2043, 2, x_2042);
x_2044 = lean_array_push(x_2020, x_2043);
x_2045 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2046 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2046, 0, x_2017);
lean_ctor_set(x_2046, 1, x_2045);
lean_ctor_set(x_2046, 2, x_2044);
x_2047 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2048 = lean_array_push(x_2047, x_2014);
x_2049 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2050 = lean_array_push(x_2048, x_2049);
x_2051 = lean_array_push(x_2050, x_2023);
x_2052 = lean_array_push(x_2051, x_2049);
x_2053 = lean_array_push(x_2052, x_2025);
x_2054 = lean_array_push(x_2053, x_2046);
x_2055 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2056 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2056, 0, x_2017);
lean_ctor_set(x_2056, 1, x_2055);
lean_ctor_set(x_2056, 2, x_2054);
x_2057 = 1;
x_2058 = lean_box(x_2057);
lean_ctor_set(x_2003, 1, x_2058);
lean_ctor_set(x_2003, 0, x_2056);
lean_ctor_set(x_2010, 0, x_2002);
return x_2010;
}
else
{
lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; uint8_t x_2084; lean_object* x_2085; 
lean_dec(x_14);
x_2059 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2059, 0, x_2017);
lean_ctor_set(x_2059, 1, x_2022);
lean_ctor_set(x_2059, 2, x_2028);
x_2060 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2061 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2061, 0, x_2012);
lean_ctor_set(x_2061, 1, x_2060);
x_2062 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2063 = lean_array_push(x_2062, x_2027);
x_2064 = lean_array_push(x_2063, x_2059);
x_2065 = lean_array_push(x_2064, x_2061);
x_2066 = lean_array_push(x_2065, x_2008);
x_2067 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2068 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2068, 0, x_2017);
lean_ctor_set(x_2068, 1, x_2067);
lean_ctor_set(x_2068, 2, x_2066);
x_2069 = lean_array_push(x_2020, x_2068);
x_2070 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2070, 0, x_2017);
lean_ctor_set(x_2070, 1, x_2022);
lean_ctor_set(x_2070, 2, x_2069);
x_2071 = lean_array_push(x_2020, x_2070);
x_2072 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2073 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2073, 0, x_2017);
lean_ctor_set(x_2073, 1, x_2072);
lean_ctor_set(x_2073, 2, x_2071);
x_2074 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2075 = lean_array_push(x_2074, x_2014);
x_2076 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2077 = lean_array_push(x_2075, x_2076);
x_2078 = lean_array_push(x_2077, x_2023);
x_2079 = lean_array_push(x_2078, x_2076);
x_2080 = lean_array_push(x_2079, x_2025);
x_2081 = lean_array_push(x_2080, x_2073);
x_2082 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2083 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2083, 0, x_2017);
lean_ctor_set(x_2083, 1, x_2082);
lean_ctor_set(x_2083, 2, x_2081);
x_2084 = 1;
x_2085 = lean_box(x_2084);
lean_ctor_set(x_2003, 1, x_2085);
lean_ctor_set(x_2003, 0, x_2083);
lean_ctor_set(x_2010, 0, x_2002);
return x_2010;
}
}
else
{
lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; uint8_t x_2130; lean_object* x_2131; lean_object* x_2132; 
x_2086 = lean_ctor_get(x_2010, 0);
x_2087 = lean_ctor_get(x_2010, 1);
lean_inc(x_2087);
lean_inc(x_2086);
lean_dec(x_2010);
x_2088 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2086);
x_2089 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2089, 0, x_2086);
lean_ctor_set(x_2089, 1, x_2088);
x_2090 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2091 = lean_array_push(x_2090, x_1995);
x_2092 = lean_box(2);
x_2093 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2094 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2094, 0, x_2092);
lean_ctor_set(x_2094, 1, x_2093);
lean_ctor_set(x_2094, 2, x_2091);
x_2095 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2096 = lean_array_push(x_2095, x_2094);
x_2097 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2098 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2098, 0, x_2092);
lean_ctor_set(x_2098, 1, x_2097);
lean_ctor_set(x_2098, 2, x_2096);
x_2099 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2086);
x_2100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2100, 0, x_2086);
lean_ctor_set(x_2100, 1, x_2099);
x_2101 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2086);
x_2102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2102, 0, x_2086);
lean_ctor_set(x_2102, 1, x_2101);
lean_inc(x_14);
x_2103 = lean_array_push(x_2095, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2104 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2104 = lean_box(0);
}
if (lean_is_scalar(x_2104)) {
 x_2105 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2105 = x_2104;
}
lean_ctor_set(x_2105, 0, x_2092);
lean_ctor_set(x_2105, 1, x_2097);
lean_ctor_set(x_2105, 2, x_2103);
x_2106 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2107, 0, x_2086);
lean_ctor_set(x_2107, 1, x_2106);
x_2108 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2109 = lean_array_push(x_2108, x_2102);
x_2110 = lean_array_push(x_2109, x_2105);
x_2111 = lean_array_push(x_2110, x_2107);
x_2112 = lean_array_push(x_2111, x_2008);
x_2113 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2114, 0, x_2092);
lean_ctor_set(x_2114, 1, x_2113);
lean_ctor_set(x_2114, 2, x_2112);
x_2115 = lean_array_push(x_2095, x_2114);
x_2116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2116, 0, x_2092);
lean_ctor_set(x_2116, 1, x_2097);
lean_ctor_set(x_2116, 2, x_2115);
x_2117 = lean_array_push(x_2095, x_2116);
x_2118 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2119, 0, x_2092);
lean_ctor_set(x_2119, 1, x_2118);
lean_ctor_set(x_2119, 2, x_2117);
x_2120 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2121 = lean_array_push(x_2120, x_2089);
x_2122 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2123 = lean_array_push(x_2121, x_2122);
x_2124 = lean_array_push(x_2123, x_2098);
x_2125 = lean_array_push(x_2124, x_2122);
x_2126 = lean_array_push(x_2125, x_2100);
x_2127 = lean_array_push(x_2126, x_2119);
x_2128 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2129, 0, x_2092);
lean_ctor_set(x_2129, 1, x_2128);
lean_ctor_set(x_2129, 2, x_2127);
x_2130 = 1;
x_2131 = lean_box(x_2130);
lean_ctor_set(x_2003, 1, x_2131);
lean_ctor_set(x_2003, 0, x_2129);
x_2132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2132, 0, x_2002);
lean_ctor_set(x_2132, 1, x_2087);
return x_2132;
}
}
else
{
lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; uint8_t x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; 
x_2133 = lean_ctor_get(x_2003, 0);
lean_inc(x_2133);
lean_dec(x_2003);
x_2134 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2004);
x_2135 = lean_ctor_get(x_2134, 0);
lean_inc(x_2135);
x_2136 = lean_ctor_get(x_2134, 1);
lean_inc(x_2136);
if (lean_is_exclusive(x_2134)) {
 lean_ctor_release(x_2134, 0);
 lean_ctor_release(x_2134, 1);
 x_2137 = x_2134;
} else {
 lean_dec_ref(x_2134);
 x_2137 = lean_box(0);
}
x_2138 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2135);
x_2139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2139, 0, x_2135);
lean_ctor_set(x_2139, 1, x_2138);
x_2140 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2141 = lean_array_push(x_2140, x_1995);
x_2142 = lean_box(2);
x_2143 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2144, 0, x_2142);
lean_ctor_set(x_2144, 1, x_2143);
lean_ctor_set(x_2144, 2, x_2141);
x_2145 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2146 = lean_array_push(x_2145, x_2144);
x_2147 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2148, 0, x_2142);
lean_ctor_set(x_2148, 1, x_2147);
lean_ctor_set(x_2148, 2, x_2146);
x_2149 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2135);
x_2150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2150, 0, x_2135);
lean_ctor_set(x_2150, 1, x_2149);
x_2151 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2135);
x_2152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2152, 0, x_2135);
lean_ctor_set(x_2152, 1, x_2151);
lean_inc(x_14);
x_2153 = lean_array_push(x_2145, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2154 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2154 = lean_box(0);
}
if (lean_is_scalar(x_2154)) {
 x_2155 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2155 = x_2154;
}
lean_ctor_set(x_2155, 0, x_2142);
lean_ctor_set(x_2155, 1, x_2147);
lean_ctor_set(x_2155, 2, x_2153);
x_2156 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2157, 0, x_2135);
lean_ctor_set(x_2157, 1, x_2156);
x_2158 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2159 = lean_array_push(x_2158, x_2152);
x_2160 = lean_array_push(x_2159, x_2155);
x_2161 = lean_array_push(x_2160, x_2157);
x_2162 = lean_array_push(x_2161, x_2133);
x_2163 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2164, 0, x_2142);
lean_ctor_set(x_2164, 1, x_2163);
lean_ctor_set(x_2164, 2, x_2162);
x_2165 = lean_array_push(x_2145, x_2164);
x_2166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2166, 0, x_2142);
lean_ctor_set(x_2166, 1, x_2147);
lean_ctor_set(x_2166, 2, x_2165);
x_2167 = lean_array_push(x_2145, x_2166);
x_2168 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2169, 0, x_2142);
lean_ctor_set(x_2169, 1, x_2168);
lean_ctor_set(x_2169, 2, x_2167);
x_2170 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2171 = lean_array_push(x_2170, x_2139);
x_2172 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2173 = lean_array_push(x_2171, x_2172);
x_2174 = lean_array_push(x_2173, x_2148);
x_2175 = lean_array_push(x_2174, x_2172);
x_2176 = lean_array_push(x_2175, x_2150);
x_2177 = lean_array_push(x_2176, x_2169);
x_2178 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2179, 0, x_2142);
lean_ctor_set(x_2179, 1, x_2178);
lean_ctor_set(x_2179, 2, x_2177);
x_2180 = 1;
x_2181 = lean_box(x_2180);
x_2182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2182, 0, x_2179);
lean_ctor_set(x_2182, 1, x_2181);
lean_ctor_set(x_2002, 1, x_2182);
if (lean_is_scalar(x_2137)) {
 x_2183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2183 = x_2137;
}
lean_ctor_set(x_2183, 0, x_2002);
lean_ctor_set(x_2183, 1, x_2136);
return x_2183;
}
}
else
{
lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; uint8_t x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; 
x_2184 = lean_ctor_get(x_2002, 0);
lean_inc(x_2184);
lean_dec(x_2002);
x_2185 = lean_ctor_get(x_2003, 0);
lean_inc(x_2185);
if (lean_is_exclusive(x_2003)) {
 lean_ctor_release(x_2003, 0);
 lean_ctor_release(x_2003, 1);
 x_2186 = x_2003;
} else {
 lean_dec_ref(x_2003);
 x_2186 = lean_box(0);
}
x_2187 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2004);
x_2188 = lean_ctor_get(x_2187, 0);
lean_inc(x_2188);
x_2189 = lean_ctor_get(x_2187, 1);
lean_inc(x_2189);
if (lean_is_exclusive(x_2187)) {
 lean_ctor_release(x_2187, 0);
 lean_ctor_release(x_2187, 1);
 x_2190 = x_2187;
} else {
 lean_dec_ref(x_2187);
 x_2190 = lean_box(0);
}
x_2191 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2188);
x_2192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2192, 0, x_2188);
lean_ctor_set(x_2192, 1, x_2191);
x_2193 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2194 = lean_array_push(x_2193, x_1995);
x_2195 = lean_box(2);
x_2196 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2197, 0, x_2195);
lean_ctor_set(x_2197, 1, x_2196);
lean_ctor_set(x_2197, 2, x_2194);
x_2198 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2199 = lean_array_push(x_2198, x_2197);
x_2200 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2201, 0, x_2195);
lean_ctor_set(x_2201, 1, x_2200);
lean_ctor_set(x_2201, 2, x_2199);
x_2202 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2188);
x_2203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2203, 0, x_2188);
lean_ctor_set(x_2203, 1, x_2202);
x_2204 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2188);
x_2205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2205, 0, x_2188);
lean_ctor_set(x_2205, 1, x_2204);
lean_inc(x_14);
x_2206 = lean_array_push(x_2198, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2207 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2207 = lean_box(0);
}
if (lean_is_scalar(x_2207)) {
 x_2208 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2208 = x_2207;
}
lean_ctor_set(x_2208, 0, x_2195);
lean_ctor_set(x_2208, 1, x_2200);
lean_ctor_set(x_2208, 2, x_2206);
x_2209 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2210, 0, x_2188);
lean_ctor_set(x_2210, 1, x_2209);
x_2211 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2212 = lean_array_push(x_2211, x_2205);
x_2213 = lean_array_push(x_2212, x_2208);
x_2214 = lean_array_push(x_2213, x_2210);
x_2215 = lean_array_push(x_2214, x_2185);
x_2216 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2217 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2217, 0, x_2195);
lean_ctor_set(x_2217, 1, x_2216);
lean_ctor_set(x_2217, 2, x_2215);
x_2218 = lean_array_push(x_2198, x_2217);
x_2219 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2219, 0, x_2195);
lean_ctor_set(x_2219, 1, x_2200);
lean_ctor_set(x_2219, 2, x_2218);
x_2220 = lean_array_push(x_2198, x_2219);
x_2221 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2222, 0, x_2195);
lean_ctor_set(x_2222, 1, x_2221);
lean_ctor_set(x_2222, 2, x_2220);
x_2223 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2224 = lean_array_push(x_2223, x_2192);
x_2225 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2226 = lean_array_push(x_2224, x_2225);
x_2227 = lean_array_push(x_2226, x_2201);
x_2228 = lean_array_push(x_2227, x_2225);
x_2229 = lean_array_push(x_2228, x_2203);
x_2230 = lean_array_push(x_2229, x_2222);
x_2231 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2232 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2232, 0, x_2195);
lean_ctor_set(x_2232, 1, x_2231);
lean_ctor_set(x_2232, 2, x_2230);
x_2233 = 1;
x_2234 = lean_box(x_2233);
if (lean_is_scalar(x_2186)) {
 x_2235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2235 = x_2186;
}
lean_ctor_set(x_2235, 0, x_2232);
lean_ctor_set(x_2235, 1, x_2234);
x_2236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2236, 0, x_2184);
lean_ctor_set(x_2236, 1, x_2235);
if (lean_is_scalar(x_2190)) {
 x_2237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2237 = x_2190;
}
lean_ctor_set(x_2237, 0, x_2236);
lean_ctor_set(x_2237, 1, x_2189);
return x_2237;
}
}
}
}
else
{
lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; 
lean_dec(x_232);
lean_inc(x_5);
lean_inc(x_14);
x_2238 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2239 = lean_ctor_get(x_2238, 0);
lean_inc(x_2239);
x_2240 = lean_ctor_get(x_2238, 1);
lean_inc(x_2240);
lean_dec(x_2238);
x_2241 = lean_unsigned_to_nat(1u);
x_2242 = lean_nat_add(x_3, x_2241);
lean_dec(x_3);
x_2243 = l_Lean_Elab_Term_mkExplicitBinder(x_2239, x_14);
x_2244 = lean_array_push(x_4, x_2243);
x_3 = x_2242;
x_4 = x_2244;
x_6 = x_2240;
goto _start;
}
}
else
{
lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; 
lean_dec(x_232);
x_2246 = lean_unsigned_to_nat(1u);
x_2247 = lean_nat_add(x_3, x_2246);
lean_dec(x_3);
x_2248 = lean_array_push(x_4, x_14);
x_3 = x_2247;
x_4 = x_2248;
goto _start;
}
}
else
{
lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; 
lean_dec(x_232);
x_2250 = lean_unsigned_to_nat(1u);
x_2251 = lean_nat_add(x_3, x_2250);
lean_dec(x_3);
x_2252 = lean_array_push(x_4, x_14);
x_3 = x_2251;
x_4 = x_2252;
goto _start;
}
}
else
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; 
lean_dec(x_232);
x_2254 = lean_unsigned_to_nat(1u);
x_2255 = lean_nat_add(x_3, x_2254);
lean_dec(x_3);
x_2256 = lean_array_push(x_4, x_14);
x_3 = x_2255;
x_4 = x_2256;
goto _start;
}
}
else
{
lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; 
lean_dec(x_232);
x_2258 = lean_unsigned_to_nat(1u);
x_2259 = lean_nat_add(x_3, x_2258);
lean_dec(x_3);
x_2260 = lean_array_push(x_4, x_14);
x_3 = x_2259;
x_4 = x_2260;
goto _start;
}
}
else
{
lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; 
lean_dec(x_232);
x_2262 = lean_unsigned_to_nat(1u);
x_2263 = lean_nat_add(x_3, x_2262);
lean_dec(x_3);
x_2264 = lean_array_push(x_4, x_14);
x_3 = x_2263;
x_4 = x_2264;
goto _start;
}
}
}
}
}
else
{
lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; uint8_t x_2278; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_inc(x_5);
lean_inc(x_14);
x_2266 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2267 = lean_ctor_get(x_2266, 0);
lean_inc(x_2267);
x_2268 = lean_ctor_get(x_2266, 1);
lean_inc(x_2268);
lean_dec(x_2266);
x_2269 = lean_unsigned_to_nat(1u);
x_2270 = lean_nat_add(x_3, x_2269);
lean_dec(x_3);
lean_inc(x_14);
x_2271 = l_Lean_mkHole(x_14);
lean_inc(x_2267);
x_2272 = l_Lean_Elab_Term_mkExplicitBinder(x_2267, x_2271);
x_2273 = lean_array_push(x_4, x_2272);
lean_inc(x_5);
x_2274 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2270, x_2273, x_5, x_2268);
x_2275 = lean_ctor_get(x_2274, 0);
lean_inc(x_2275);
x_2276 = lean_ctor_get(x_2275, 1);
lean_inc(x_2276);
x_2277 = lean_ctor_get(x_2274, 1);
lean_inc(x_2277);
lean_dec(x_2274);
x_2278 = !lean_is_exclusive(x_2275);
if (x_2278 == 0)
{
lean_object* x_2279; uint8_t x_2280; 
x_2279 = lean_ctor_get(x_2275, 1);
lean_dec(x_2279);
x_2280 = !lean_is_exclusive(x_2276);
if (x_2280 == 0)
{
lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; uint8_t x_2284; 
x_2281 = lean_ctor_get(x_2276, 0);
x_2282 = lean_ctor_get(x_2276, 1);
lean_dec(x_2282);
x_2283 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2277);
x_2284 = !lean_is_exclusive(x_2283);
if (x_2284 == 0)
{
lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; uint8_t x_2302; 
x_2285 = lean_ctor_get(x_2283, 0);
x_2286 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2285);
x_2287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2287, 0, x_2285);
lean_ctor_set(x_2287, 1, x_2286);
x_2288 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2289 = lean_array_push(x_2288, x_2267);
x_2290 = lean_box(2);
x_2291 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2292, 0, x_2290);
lean_ctor_set(x_2292, 1, x_2291);
lean_ctor_set(x_2292, 2, x_2289);
x_2293 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2294 = lean_array_push(x_2293, x_2292);
x_2295 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2296 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2296, 0, x_2290);
lean_ctor_set(x_2296, 1, x_2295);
lean_ctor_set(x_2296, 2, x_2294);
x_2297 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2285);
x_2298 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2298, 0, x_2285);
lean_ctor_set(x_2298, 1, x_2297);
x_2299 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2285);
x_2300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2300, 0, x_2285);
lean_ctor_set(x_2300, 1, x_2299);
lean_inc(x_14);
x_2301 = lean_array_push(x_2293, x_14);
x_2302 = !lean_is_exclusive(x_14);
if (x_2302 == 0)
{
lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; uint8_t x_2330; lean_object* x_2331; 
x_2303 = lean_ctor_get(x_14, 2);
lean_dec(x_2303);
x_2304 = lean_ctor_get(x_14, 1);
lean_dec(x_2304);
x_2305 = lean_ctor_get(x_14, 0);
lean_dec(x_2305);
lean_ctor_set(x_14, 2, x_2301);
lean_ctor_set(x_14, 1, x_2295);
lean_ctor_set(x_14, 0, x_2290);
x_2306 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2307, 0, x_2285);
lean_ctor_set(x_2307, 1, x_2306);
x_2308 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2309 = lean_array_push(x_2308, x_2300);
x_2310 = lean_array_push(x_2309, x_14);
x_2311 = lean_array_push(x_2310, x_2307);
x_2312 = lean_array_push(x_2311, x_2281);
x_2313 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2314, 0, x_2290);
lean_ctor_set(x_2314, 1, x_2313);
lean_ctor_set(x_2314, 2, x_2312);
x_2315 = lean_array_push(x_2293, x_2314);
x_2316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2316, 0, x_2290);
lean_ctor_set(x_2316, 1, x_2295);
lean_ctor_set(x_2316, 2, x_2315);
x_2317 = lean_array_push(x_2293, x_2316);
x_2318 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2319, 0, x_2290);
lean_ctor_set(x_2319, 1, x_2318);
lean_ctor_set(x_2319, 2, x_2317);
x_2320 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2321 = lean_array_push(x_2320, x_2287);
x_2322 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2323 = lean_array_push(x_2321, x_2322);
x_2324 = lean_array_push(x_2323, x_2296);
x_2325 = lean_array_push(x_2324, x_2322);
x_2326 = lean_array_push(x_2325, x_2298);
x_2327 = lean_array_push(x_2326, x_2319);
x_2328 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2329 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2329, 0, x_2290);
lean_ctor_set(x_2329, 1, x_2328);
lean_ctor_set(x_2329, 2, x_2327);
x_2330 = 1;
x_2331 = lean_box(x_2330);
lean_ctor_set(x_2276, 1, x_2331);
lean_ctor_set(x_2276, 0, x_2329);
lean_ctor_set(x_2283, 0, x_2275);
return x_2283;
}
else
{
lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; uint8_t x_2357; lean_object* x_2358; 
lean_dec(x_14);
x_2332 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2332, 0, x_2290);
lean_ctor_set(x_2332, 1, x_2295);
lean_ctor_set(x_2332, 2, x_2301);
x_2333 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2334, 0, x_2285);
lean_ctor_set(x_2334, 1, x_2333);
x_2335 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2336 = lean_array_push(x_2335, x_2300);
x_2337 = lean_array_push(x_2336, x_2332);
x_2338 = lean_array_push(x_2337, x_2334);
x_2339 = lean_array_push(x_2338, x_2281);
x_2340 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2341 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2341, 0, x_2290);
lean_ctor_set(x_2341, 1, x_2340);
lean_ctor_set(x_2341, 2, x_2339);
x_2342 = lean_array_push(x_2293, x_2341);
x_2343 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2343, 0, x_2290);
lean_ctor_set(x_2343, 1, x_2295);
lean_ctor_set(x_2343, 2, x_2342);
x_2344 = lean_array_push(x_2293, x_2343);
x_2345 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2346 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2346, 0, x_2290);
lean_ctor_set(x_2346, 1, x_2345);
lean_ctor_set(x_2346, 2, x_2344);
x_2347 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2348 = lean_array_push(x_2347, x_2287);
x_2349 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2350 = lean_array_push(x_2348, x_2349);
x_2351 = lean_array_push(x_2350, x_2296);
x_2352 = lean_array_push(x_2351, x_2349);
x_2353 = lean_array_push(x_2352, x_2298);
x_2354 = lean_array_push(x_2353, x_2346);
x_2355 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2356 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2356, 0, x_2290);
lean_ctor_set(x_2356, 1, x_2355);
lean_ctor_set(x_2356, 2, x_2354);
x_2357 = 1;
x_2358 = lean_box(x_2357);
lean_ctor_set(x_2276, 1, x_2358);
lean_ctor_set(x_2276, 0, x_2356);
lean_ctor_set(x_2283, 0, x_2275);
return x_2283;
}
}
else
{
lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; uint8_t x_2403; lean_object* x_2404; lean_object* x_2405; 
x_2359 = lean_ctor_get(x_2283, 0);
x_2360 = lean_ctor_get(x_2283, 1);
lean_inc(x_2360);
lean_inc(x_2359);
lean_dec(x_2283);
x_2361 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2359);
x_2362 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2362, 0, x_2359);
lean_ctor_set(x_2362, 1, x_2361);
x_2363 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2364 = lean_array_push(x_2363, x_2267);
x_2365 = lean_box(2);
x_2366 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2367 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2367, 0, x_2365);
lean_ctor_set(x_2367, 1, x_2366);
lean_ctor_set(x_2367, 2, x_2364);
x_2368 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2369 = lean_array_push(x_2368, x_2367);
x_2370 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2371 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2371, 0, x_2365);
lean_ctor_set(x_2371, 1, x_2370);
lean_ctor_set(x_2371, 2, x_2369);
x_2372 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2359);
x_2373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2373, 0, x_2359);
lean_ctor_set(x_2373, 1, x_2372);
x_2374 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2359);
x_2375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2375, 0, x_2359);
lean_ctor_set(x_2375, 1, x_2374);
lean_inc(x_14);
x_2376 = lean_array_push(x_2368, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2377 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2377 = lean_box(0);
}
if (lean_is_scalar(x_2377)) {
 x_2378 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2378 = x_2377;
}
lean_ctor_set(x_2378, 0, x_2365);
lean_ctor_set(x_2378, 1, x_2370);
lean_ctor_set(x_2378, 2, x_2376);
x_2379 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2380 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2380, 0, x_2359);
lean_ctor_set(x_2380, 1, x_2379);
x_2381 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2382 = lean_array_push(x_2381, x_2375);
x_2383 = lean_array_push(x_2382, x_2378);
x_2384 = lean_array_push(x_2383, x_2380);
x_2385 = lean_array_push(x_2384, x_2281);
x_2386 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2387 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2387, 0, x_2365);
lean_ctor_set(x_2387, 1, x_2386);
lean_ctor_set(x_2387, 2, x_2385);
x_2388 = lean_array_push(x_2368, x_2387);
x_2389 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2389, 0, x_2365);
lean_ctor_set(x_2389, 1, x_2370);
lean_ctor_set(x_2389, 2, x_2388);
x_2390 = lean_array_push(x_2368, x_2389);
x_2391 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2392 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2392, 0, x_2365);
lean_ctor_set(x_2392, 1, x_2391);
lean_ctor_set(x_2392, 2, x_2390);
x_2393 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2394 = lean_array_push(x_2393, x_2362);
x_2395 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2396 = lean_array_push(x_2394, x_2395);
x_2397 = lean_array_push(x_2396, x_2371);
x_2398 = lean_array_push(x_2397, x_2395);
x_2399 = lean_array_push(x_2398, x_2373);
x_2400 = lean_array_push(x_2399, x_2392);
x_2401 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2402 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2402, 0, x_2365);
lean_ctor_set(x_2402, 1, x_2401);
lean_ctor_set(x_2402, 2, x_2400);
x_2403 = 1;
x_2404 = lean_box(x_2403);
lean_ctor_set(x_2276, 1, x_2404);
lean_ctor_set(x_2276, 0, x_2402);
x_2405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2405, 0, x_2275);
lean_ctor_set(x_2405, 1, x_2360);
return x_2405;
}
}
else
{
lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; uint8_t x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; 
x_2406 = lean_ctor_get(x_2276, 0);
lean_inc(x_2406);
lean_dec(x_2276);
x_2407 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2277);
x_2408 = lean_ctor_get(x_2407, 0);
lean_inc(x_2408);
x_2409 = lean_ctor_get(x_2407, 1);
lean_inc(x_2409);
if (lean_is_exclusive(x_2407)) {
 lean_ctor_release(x_2407, 0);
 lean_ctor_release(x_2407, 1);
 x_2410 = x_2407;
} else {
 lean_dec_ref(x_2407);
 x_2410 = lean_box(0);
}
x_2411 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2408);
x_2412 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2412, 0, x_2408);
lean_ctor_set(x_2412, 1, x_2411);
x_2413 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2414 = lean_array_push(x_2413, x_2267);
x_2415 = lean_box(2);
x_2416 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2417 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2417, 0, x_2415);
lean_ctor_set(x_2417, 1, x_2416);
lean_ctor_set(x_2417, 2, x_2414);
x_2418 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2419 = lean_array_push(x_2418, x_2417);
x_2420 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2421 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2421, 0, x_2415);
lean_ctor_set(x_2421, 1, x_2420);
lean_ctor_set(x_2421, 2, x_2419);
x_2422 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2408);
x_2423 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2423, 0, x_2408);
lean_ctor_set(x_2423, 1, x_2422);
x_2424 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2408);
x_2425 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2425, 0, x_2408);
lean_ctor_set(x_2425, 1, x_2424);
lean_inc(x_14);
x_2426 = lean_array_push(x_2418, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2427 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2427 = lean_box(0);
}
if (lean_is_scalar(x_2427)) {
 x_2428 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2428 = x_2427;
}
lean_ctor_set(x_2428, 0, x_2415);
lean_ctor_set(x_2428, 1, x_2420);
lean_ctor_set(x_2428, 2, x_2426);
x_2429 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2430 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2430, 0, x_2408);
lean_ctor_set(x_2430, 1, x_2429);
x_2431 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2432 = lean_array_push(x_2431, x_2425);
x_2433 = lean_array_push(x_2432, x_2428);
x_2434 = lean_array_push(x_2433, x_2430);
x_2435 = lean_array_push(x_2434, x_2406);
x_2436 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2437 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2437, 0, x_2415);
lean_ctor_set(x_2437, 1, x_2436);
lean_ctor_set(x_2437, 2, x_2435);
x_2438 = lean_array_push(x_2418, x_2437);
x_2439 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2439, 0, x_2415);
lean_ctor_set(x_2439, 1, x_2420);
lean_ctor_set(x_2439, 2, x_2438);
x_2440 = lean_array_push(x_2418, x_2439);
x_2441 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2442 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2442, 0, x_2415);
lean_ctor_set(x_2442, 1, x_2441);
lean_ctor_set(x_2442, 2, x_2440);
x_2443 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2444 = lean_array_push(x_2443, x_2412);
x_2445 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2446 = lean_array_push(x_2444, x_2445);
x_2447 = lean_array_push(x_2446, x_2421);
x_2448 = lean_array_push(x_2447, x_2445);
x_2449 = lean_array_push(x_2448, x_2423);
x_2450 = lean_array_push(x_2449, x_2442);
x_2451 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2452 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2452, 0, x_2415);
lean_ctor_set(x_2452, 1, x_2451);
lean_ctor_set(x_2452, 2, x_2450);
x_2453 = 1;
x_2454 = lean_box(x_2453);
x_2455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2455, 0, x_2452);
lean_ctor_set(x_2455, 1, x_2454);
lean_ctor_set(x_2275, 1, x_2455);
if (lean_is_scalar(x_2410)) {
 x_2456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2456 = x_2410;
}
lean_ctor_set(x_2456, 0, x_2275);
lean_ctor_set(x_2456, 1, x_2409);
return x_2456;
}
}
else
{
lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; uint8_t x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; 
x_2457 = lean_ctor_get(x_2275, 0);
lean_inc(x_2457);
lean_dec(x_2275);
x_2458 = lean_ctor_get(x_2276, 0);
lean_inc(x_2458);
if (lean_is_exclusive(x_2276)) {
 lean_ctor_release(x_2276, 0);
 lean_ctor_release(x_2276, 1);
 x_2459 = x_2276;
} else {
 lean_dec_ref(x_2276);
 x_2459 = lean_box(0);
}
x_2460 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2277);
x_2461 = lean_ctor_get(x_2460, 0);
lean_inc(x_2461);
x_2462 = lean_ctor_get(x_2460, 1);
lean_inc(x_2462);
if (lean_is_exclusive(x_2460)) {
 lean_ctor_release(x_2460, 0);
 lean_ctor_release(x_2460, 1);
 x_2463 = x_2460;
} else {
 lean_dec_ref(x_2460);
 x_2463 = lean_box(0);
}
x_2464 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2461);
x_2465 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2465, 0, x_2461);
lean_ctor_set(x_2465, 1, x_2464);
x_2466 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2467 = lean_array_push(x_2466, x_2267);
x_2468 = lean_box(2);
x_2469 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2470 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2470, 0, x_2468);
lean_ctor_set(x_2470, 1, x_2469);
lean_ctor_set(x_2470, 2, x_2467);
x_2471 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2472 = lean_array_push(x_2471, x_2470);
x_2473 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2474 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2474, 0, x_2468);
lean_ctor_set(x_2474, 1, x_2473);
lean_ctor_set(x_2474, 2, x_2472);
x_2475 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2461);
x_2476 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2476, 0, x_2461);
lean_ctor_set(x_2476, 1, x_2475);
x_2477 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2461);
x_2478 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2478, 0, x_2461);
lean_ctor_set(x_2478, 1, x_2477);
lean_inc(x_14);
x_2479 = lean_array_push(x_2471, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2480 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2480 = lean_box(0);
}
if (lean_is_scalar(x_2480)) {
 x_2481 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2481 = x_2480;
}
lean_ctor_set(x_2481, 0, x_2468);
lean_ctor_set(x_2481, 1, x_2473);
lean_ctor_set(x_2481, 2, x_2479);
x_2482 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2483 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2483, 0, x_2461);
lean_ctor_set(x_2483, 1, x_2482);
x_2484 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2485 = lean_array_push(x_2484, x_2478);
x_2486 = lean_array_push(x_2485, x_2481);
x_2487 = lean_array_push(x_2486, x_2483);
x_2488 = lean_array_push(x_2487, x_2458);
x_2489 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2490 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2490, 0, x_2468);
lean_ctor_set(x_2490, 1, x_2489);
lean_ctor_set(x_2490, 2, x_2488);
x_2491 = lean_array_push(x_2471, x_2490);
x_2492 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2492, 0, x_2468);
lean_ctor_set(x_2492, 1, x_2473);
lean_ctor_set(x_2492, 2, x_2491);
x_2493 = lean_array_push(x_2471, x_2492);
x_2494 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2495 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2495, 0, x_2468);
lean_ctor_set(x_2495, 1, x_2494);
lean_ctor_set(x_2495, 2, x_2493);
x_2496 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2497 = lean_array_push(x_2496, x_2465);
x_2498 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2499 = lean_array_push(x_2497, x_2498);
x_2500 = lean_array_push(x_2499, x_2474);
x_2501 = lean_array_push(x_2500, x_2498);
x_2502 = lean_array_push(x_2501, x_2476);
x_2503 = lean_array_push(x_2502, x_2495);
x_2504 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2505 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2505, 0, x_2468);
lean_ctor_set(x_2505, 1, x_2504);
lean_ctor_set(x_2505, 2, x_2503);
x_2506 = 1;
x_2507 = lean_box(x_2506);
if (lean_is_scalar(x_2459)) {
 x_2508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2508 = x_2459;
}
lean_ctor_set(x_2508, 0, x_2505);
lean_ctor_set(x_2508, 1, x_2507);
x_2509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2509, 0, x_2457);
lean_ctor_set(x_2509, 1, x_2508);
if (lean_is_scalar(x_2463)) {
 x_2510 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2510 = x_2463;
}
lean_ctor_set(x_2510, 0, x_2509);
lean_ctor_set(x_2510, 1, x_2462);
return x_2510;
}
}
}
else
{
lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; uint8_t x_2523; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_inc(x_5);
lean_inc(x_14);
x_2511 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2512 = lean_ctor_get(x_2511, 0);
lean_inc(x_2512);
x_2513 = lean_ctor_get(x_2511, 1);
lean_inc(x_2513);
lean_dec(x_2511);
x_2514 = lean_unsigned_to_nat(1u);
x_2515 = lean_nat_add(x_3, x_2514);
lean_dec(x_3);
lean_inc(x_14);
x_2516 = l_Lean_mkHole(x_14);
lean_inc(x_2512);
x_2517 = l_Lean_Elab_Term_mkExplicitBinder(x_2512, x_2516);
x_2518 = lean_array_push(x_4, x_2517);
lean_inc(x_5);
x_2519 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2515, x_2518, x_5, x_2513);
x_2520 = lean_ctor_get(x_2519, 0);
lean_inc(x_2520);
x_2521 = lean_ctor_get(x_2520, 1);
lean_inc(x_2521);
x_2522 = lean_ctor_get(x_2519, 1);
lean_inc(x_2522);
lean_dec(x_2519);
x_2523 = !lean_is_exclusive(x_2520);
if (x_2523 == 0)
{
lean_object* x_2524; uint8_t x_2525; 
x_2524 = lean_ctor_get(x_2520, 1);
lean_dec(x_2524);
x_2525 = !lean_is_exclusive(x_2521);
if (x_2525 == 0)
{
lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; uint8_t x_2529; 
x_2526 = lean_ctor_get(x_2521, 0);
x_2527 = lean_ctor_get(x_2521, 1);
lean_dec(x_2527);
x_2528 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2522);
x_2529 = !lean_is_exclusive(x_2528);
if (x_2529 == 0)
{
lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; uint8_t x_2547; 
x_2530 = lean_ctor_get(x_2528, 0);
x_2531 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2530);
x_2532 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2532, 0, x_2530);
lean_ctor_set(x_2532, 1, x_2531);
x_2533 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2534 = lean_array_push(x_2533, x_2512);
x_2535 = lean_box(2);
x_2536 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2537 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2537, 0, x_2535);
lean_ctor_set(x_2537, 1, x_2536);
lean_ctor_set(x_2537, 2, x_2534);
x_2538 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2539 = lean_array_push(x_2538, x_2537);
x_2540 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2541 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2541, 0, x_2535);
lean_ctor_set(x_2541, 1, x_2540);
lean_ctor_set(x_2541, 2, x_2539);
x_2542 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2530);
x_2543 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2543, 0, x_2530);
lean_ctor_set(x_2543, 1, x_2542);
x_2544 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2530);
x_2545 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2545, 0, x_2530);
lean_ctor_set(x_2545, 1, x_2544);
lean_inc(x_14);
x_2546 = lean_array_push(x_2538, x_14);
x_2547 = !lean_is_exclusive(x_14);
if (x_2547 == 0)
{
lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; uint8_t x_2575; lean_object* x_2576; 
x_2548 = lean_ctor_get(x_14, 2);
lean_dec(x_2548);
x_2549 = lean_ctor_get(x_14, 1);
lean_dec(x_2549);
x_2550 = lean_ctor_get(x_14, 0);
lean_dec(x_2550);
lean_ctor_set(x_14, 2, x_2546);
lean_ctor_set(x_14, 1, x_2540);
lean_ctor_set(x_14, 0, x_2535);
x_2551 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2552 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2552, 0, x_2530);
lean_ctor_set(x_2552, 1, x_2551);
x_2553 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2554 = lean_array_push(x_2553, x_2545);
x_2555 = lean_array_push(x_2554, x_14);
x_2556 = lean_array_push(x_2555, x_2552);
x_2557 = lean_array_push(x_2556, x_2526);
x_2558 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2559 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2559, 0, x_2535);
lean_ctor_set(x_2559, 1, x_2558);
lean_ctor_set(x_2559, 2, x_2557);
x_2560 = lean_array_push(x_2538, x_2559);
x_2561 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2561, 0, x_2535);
lean_ctor_set(x_2561, 1, x_2540);
lean_ctor_set(x_2561, 2, x_2560);
x_2562 = lean_array_push(x_2538, x_2561);
x_2563 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2564 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2564, 0, x_2535);
lean_ctor_set(x_2564, 1, x_2563);
lean_ctor_set(x_2564, 2, x_2562);
x_2565 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2566 = lean_array_push(x_2565, x_2532);
x_2567 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2568 = lean_array_push(x_2566, x_2567);
x_2569 = lean_array_push(x_2568, x_2541);
x_2570 = lean_array_push(x_2569, x_2567);
x_2571 = lean_array_push(x_2570, x_2543);
x_2572 = lean_array_push(x_2571, x_2564);
x_2573 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2574 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2574, 0, x_2535);
lean_ctor_set(x_2574, 1, x_2573);
lean_ctor_set(x_2574, 2, x_2572);
x_2575 = 1;
x_2576 = lean_box(x_2575);
lean_ctor_set(x_2521, 1, x_2576);
lean_ctor_set(x_2521, 0, x_2574);
lean_ctor_set(x_2528, 0, x_2520);
return x_2528;
}
else
{
lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; uint8_t x_2602; lean_object* x_2603; 
lean_dec(x_14);
x_2577 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2577, 0, x_2535);
lean_ctor_set(x_2577, 1, x_2540);
lean_ctor_set(x_2577, 2, x_2546);
x_2578 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2579 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2579, 0, x_2530);
lean_ctor_set(x_2579, 1, x_2578);
x_2580 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2581 = lean_array_push(x_2580, x_2545);
x_2582 = lean_array_push(x_2581, x_2577);
x_2583 = lean_array_push(x_2582, x_2579);
x_2584 = lean_array_push(x_2583, x_2526);
x_2585 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2586 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2586, 0, x_2535);
lean_ctor_set(x_2586, 1, x_2585);
lean_ctor_set(x_2586, 2, x_2584);
x_2587 = lean_array_push(x_2538, x_2586);
x_2588 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2588, 0, x_2535);
lean_ctor_set(x_2588, 1, x_2540);
lean_ctor_set(x_2588, 2, x_2587);
x_2589 = lean_array_push(x_2538, x_2588);
x_2590 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2591 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2591, 0, x_2535);
lean_ctor_set(x_2591, 1, x_2590);
lean_ctor_set(x_2591, 2, x_2589);
x_2592 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2593 = lean_array_push(x_2592, x_2532);
x_2594 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2595 = lean_array_push(x_2593, x_2594);
x_2596 = lean_array_push(x_2595, x_2541);
x_2597 = lean_array_push(x_2596, x_2594);
x_2598 = lean_array_push(x_2597, x_2543);
x_2599 = lean_array_push(x_2598, x_2591);
x_2600 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2601 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2601, 0, x_2535);
lean_ctor_set(x_2601, 1, x_2600);
lean_ctor_set(x_2601, 2, x_2599);
x_2602 = 1;
x_2603 = lean_box(x_2602);
lean_ctor_set(x_2521, 1, x_2603);
lean_ctor_set(x_2521, 0, x_2601);
lean_ctor_set(x_2528, 0, x_2520);
return x_2528;
}
}
else
{
lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; uint8_t x_2648; lean_object* x_2649; lean_object* x_2650; 
x_2604 = lean_ctor_get(x_2528, 0);
x_2605 = lean_ctor_get(x_2528, 1);
lean_inc(x_2605);
lean_inc(x_2604);
lean_dec(x_2528);
x_2606 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2604);
x_2607 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2607, 0, x_2604);
lean_ctor_set(x_2607, 1, x_2606);
x_2608 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2609 = lean_array_push(x_2608, x_2512);
x_2610 = lean_box(2);
x_2611 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2612 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2612, 0, x_2610);
lean_ctor_set(x_2612, 1, x_2611);
lean_ctor_set(x_2612, 2, x_2609);
x_2613 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2614 = lean_array_push(x_2613, x_2612);
x_2615 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2616 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2616, 0, x_2610);
lean_ctor_set(x_2616, 1, x_2615);
lean_ctor_set(x_2616, 2, x_2614);
x_2617 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2604);
x_2618 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2618, 0, x_2604);
lean_ctor_set(x_2618, 1, x_2617);
x_2619 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2604);
x_2620 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2620, 0, x_2604);
lean_ctor_set(x_2620, 1, x_2619);
lean_inc(x_14);
x_2621 = lean_array_push(x_2613, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2622 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2622 = lean_box(0);
}
if (lean_is_scalar(x_2622)) {
 x_2623 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2623 = x_2622;
}
lean_ctor_set(x_2623, 0, x_2610);
lean_ctor_set(x_2623, 1, x_2615);
lean_ctor_set(x_2623, 2, x_2621);
x_2624 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2625 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2625, 0, x_2604);
lean_ctor_set(x_2625, 1, x_2624);
x_2626 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2627 = lean_array_push(x_2626, x_2620);
x_2628 = lean_array_push(x_2627, x_2623);
x_2629 = lean_array_push(x_2628, x_2625);
x_2630 = lean_array_push(x_2629, x_2526);
x_2631 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2632 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2632, 0, x_2610);
lean_ctor_set(x_2632, 1, x_2631);
lean_ctor_set(x_2632, 2, x_2630);
x_2633 = lean_array_push(x_2613, x_2632);
x_2634 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2634, 0, x_2610);
lean_ctor_set(x_2634, 1, x_2615);
lean_ctor_set(x_2634, 2, x_2633);
x_2635 = lean_array_push(x_2613, x_2634);
x_2636 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2637 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2637, 0, x_2610);
lean_ctor_set(x_2637, 1, x_2636);
lean_ctor_set(x_2637, 2, x_2635);
x_2638 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2639 = lean_array_push(x_2638, x_2607);
x_2640 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2641 = lean_array_push(x_2639, x_2640);
x_2642 = lean_array_push(x_2641, x_2616);
x_2643 = lean_array_push(x_2642, x_2640);
x_2644 = lean_array_push(x_2643, x_2618);
x_2645 = lean_array_push(x_2644, x_2637);
x_2646 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2647 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2647, 0, x_2610);
lean_ctor_set(x_2647, 1, x_2646);
lean_ctor_set(x_2647, 2, x_2645);
x_2648 = 1;
x_2649 = lean_box(x_2648);
lean_ctor_set(x_2521, 1, x_2649);
lean_ctor_set(x_2521, 0, x_2647);
x_2650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2650, 0, x_2520);
lean_ctor_set(x_2650, 1, x_2605);
return x_2650;
}
}
else
{
lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; uint8_t x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; 
x_2651 = lean_ctor_get(x_2521, 0);
lean_inc(x_2651);
lean_dec(x_2521);
x_2652 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2522);
x_2653 = lean_ctor_get(x_2652, 0);
lean_inc(x_2653);
x_2654 = lean_ctor_get(x_2652, 1);
lean_inc(x_2654);
if (lean_is_exclusive(x_2652)) {
 lean_ctor_release(x_2652, 0);
 lean_ctor_release(x_2652, 1);
 x_2655 = x_2652;
} else {
 lean_dec_ref(x_2652);
 x_2655 = lean_box(0);
}
x_2656 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2653);
x_2657 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2657, 0, x_2653);
lean_ctor_set(x_2657, 1, x_2656);
x_2658 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2659 = lean_array_push(x_2658, x_2512);
x_2660 = lean_box(2);
x_2661 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2662 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2662, 0, x_2660);
lean_ctor_set(x_2662, 1, x_2661);
lean_ctor_set(x_2662, 2, x_2659);
x_2663 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2664 = lean_array_push(x_2663, x_2662);
x_2665 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2666 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2666, 0, x_2660);
lean_ctor_set(x_2666, 1, x_2665);
lean_ctor_set(x_2666, 2, x_2664);
x_2667 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2653);
x_2668 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2668, 0, x_2653);
lean_ctor_set(x_2668, 1, x_2667);
x_2669 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2653);
x_2670 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2670, 0, x_2653);
lean_ctor_set(x_2670, 1, x_2669);
lean_inc(x_14);
x_2671 = lean_array_push(x_2663, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2672 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2672 = lean_box(0);
}
if (lean_is_scalar(x_2672)) {
 x_2673 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2673 = x_2672;
}
lean_ctor_set(x_2673, 0, x_2660);
lean_ctor_set(x_2673, 1, x_2665);
lean_ctor_set(x_2673, 2, x_2671);
x_2674 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2675 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2675, 0, x_2653);
lean_ctor_set(x_2675, 1, x_2674);
x_2676 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2677 = lean_array_push(x_2676, x_2670);
x_2678 = lean_array_push(x_2677, x_2673);
x_2679 = lean_array_push(x_2678, x_2675);
x_2680 = lean_array_push(x_2679, x_2651);
x_2681 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2682 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2682, 0, x_2660);
lean_ctor_set(x_2682, 1, x_2681);
lean_ctor_set(x_2682, 2, x_2680);
x_2683 = lean_array_push(x_2663, x_2682);
x_2684 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2684, 0, x_2660);
lean_ctor_set(x_2684, 1, x_2665);
lean_ctor_set(x_2684, 2, x_2683);
x_2685 = lean_array_push(x_2663, x_2684);
x_2686 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2687 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2687, 0, x_2660);
lean_ctor_set(x_2687, 1, x_2686);
lean_ctor_set(x_2687, 2, x_2685);
x_2688 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2689 = lean_array_push(x_2688, x_2657);
x_2690 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2691 = lean_array_push(x_2689, x_2690);
x_2692 = lean_array_push(x_2691, x_2666);
x_2693 = lean_array_push(x_2692, x_2690);
x_2694 = lean_array_push(x_2693, x_2668);
x_2695 = lean_array_push(x_2694, x_2687);
x_2696 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2697 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2697, 0, x_2660);
lean_ctor_set(x_2697, 1, x_2696);
lean_ctor_set(x_2697, 2, x_2695);
x_2698 = 1;
x_2699 = lean_box(x_2698);
x_2700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2700, 0, x_2697);
lean_ctor_set(x_2700, 1, x_2699);
lean_ctor_set(x_2520, 1, x_2700);
if (lean_is_scalar(x_2655)) {
 x_2701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2701 = x_2655;
}
lean_ctor_set(x_2701, 0, x_2520);
lean_ctor_set(x_2701, 1, x_2654);
return x_2701;
}
}
else
{
lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; uint8_t x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; 
x_2702 = lean_ctor_get(x_2520, 0);
lean_inc(x_2702);
lean_dec(x_2520);
x_2703 = lean_ctor_get(x_2521, 0);
lean_inc(x_2703);
if (lean_is_exclusive(x_2521)) {
 lean_ctor_release(x_2521, 0);
 lean_ctor_release(x_2521, 1);
 x_2704 = x_2521;
} else {
 lean_dec_ref(x_2521);
 x_2704 = lean_box(0);
}
x_2705 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2522);
x_2706 = lean_ctor_get(x_2705, 0);
lean_inc(x_2706);
x_2707 = lean_ctor_get(x_2705, 1);
lean_inc(x_2707);
if (lean_is_exclusive(x_2705)) {
 lean_ctor_release(x_2705, 0);
 lean_ctor_release(x_2705, 1);
 x_2708 = x_2705;
} else {
 lean_dec_ref(x_2705);
 x_2708 = lean_box(0);
}
x_2709 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2706);
x_2710 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2710, 0, x_2706);
lean_ctor_set(x_2710, 1, x_2709);
x_2711 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2712 = lean_array_push(x_2711, x_2512);
x_2713 = lean_box(2);
x_2714 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2715 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2715, 0, x_2713);
lean_ctor_set(x_2715, 1, x_2714);
lean_ctor_set(x_2715, 2, x_2712);
x_2716 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2717 = lean_array_push(x_2716, x_2715);
x_2718 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2719 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2719, 0, x_2713);
lean_ctor_set(x_2719, 1, x_2718);
lean_ctor_set(x_2719, 2, x_2717);
x_2720 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2706);
x_2721 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2721, 0, x_2706);
lean_ctor_set(x_2721, 1, x_2720);
x_2722 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2706);
x_2723 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2723, 0, x_2706);
lean_ctor_set(x_2723, 1, x_2722);
lean_inc(x_14);
x_2724 = lean_array_push(x_2716, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2725 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2725 = lean_box(0);
}
if (lean_is_scalar(x_2725)) {
 x_2726 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2726 = x_2725;
}
lean_ctor_set(x_2726, 0, x_2713);
lean_ctor_set(x_2726, 1, x_2718);
lean_ctor_set(x_2726, 2, x_2724);
x_2727 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2728 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2728, 0, x_2706);
lean_ctor_set(x_2728, 1, x_2727);
x_2729 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2730 = lean_array_push(x_2729, x_2723);
x_2731 = lean_array_push(x_2730, x_2726);
x_2732 = lean_array_push(x_2731, x_2728);
x_2733 = lean_array_push(x_2732, x_2703);
x_2734 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2735 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2735, 0, x_2713);
lean_ctor_set(x_2735, 1, x_2734);
lean_ctor_set(x_2735, 2, x_2733);
x_2736 = lean_array_push(x_2716, x_2735);
x_2737 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2737, 0, x_2713);
lean_ctor_set(x_2737, 1, x_2718);
lean_ctor_set(x_2737, 2, x_2736);
x_2738 = lean_array_push(x_2716, x_2737);
x_2739 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2740 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2740, 0, x_2713);
lean_ctor_set(x_2740, 1, x_2739);
lean_ctor_set(x_2740, 2, x_2738);
x_2741 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2742 = lean_array_push(x_2741, x_2710);
x_2743 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2744 = lean_array_push(x_2742, x_2743);
x_2745 = lean_array_push(x_2744, x_2719);
x_2746 = lean_array_push(x_2745, x_2743);
x_2747 = lean_array_push(x_2746, x_2721);
x_2748 = lean_array_push(x_2747, x_2740);
x_2749 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2750 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2750, 0, x_2713);
lean_ctor_set(x_2750, 1, x_2749);
lean_ctor_set(x_2750, 2, x_2748);
x_2751 = 1;
x_2752 = lean_box(x_2751);
if (lean_is_scalar(x_2704)) {
 x_2753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2753 = x_2704;
}
lean_ctor_set(x_2753, 0, x_2750);
lean_ctor_set(x_2753, 1, x_2752);
x_2754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2754, 0, x_2702);
lean_ctor_set(x_2754, 1, x_2753);
if (lean_is_scalar(x_2708)) {
 x_2755 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2755 = x_2708;
}
lean_ctor_set(x_2755, 0, x_2754);
lean_ctor_set(x_2755, 1, x_2707);
return x_2755;
}
}
}
else
{
lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; uint8_t x_2768; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_inc(x_5);
lean_inc(x_14);
x_2756 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_2757 = lean_ctor_get(x_2756, 0);
lean_inc(x_2757);
x_2758 = lean_ctor_get(x_2756, 1);
lean_inc(x_2758);
lean_dec(x_2756);
x_2759 = lean_unsigned_to_nat(1u);
x_2760 = lean_nat_add(x_3, x_2759);
lean_dec(x_3);
lean_inc(x_14);
x_2761 = l_Lean_mkHole(x_14);
lean_inc(x_2757);
x_2762 = l_Lean_Elab_Term_mkExplicitBinder(x_2757, x_2761);
x_2763 = lean_array_push(x_4, x_2762);
lean_inc(x_5);
x_2764 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_2760, x_2763, x_5, x_2758);
x_2765 = lean_ctor_get(x_2764, 0);
lean_inc(x_2765);
x_2766 = lean_ctor_get(x_2765, 1);
lean_inc(x_2766);
x_2767 = lean_ctor_get(x_2764, 1);
lean_inc(x_2767);
lean_dec(x_2764);
x_2768 = !lean_is_exclusive(x_2765);
if (x_2768 == 0)
{
lean_object* x_2769; uint8_t x_2770; 
x_2769 = lean_ctor_get(x_2765, 1);
lean_dec(x_2769);
x_2770 = !lean_is_exclusive(x_2766);
if (x_2770 == 0)
{
lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; uint8_t x_2774; 
x_2771 = lean_ctor_get(x_2766, 0);
x_2772 = lean_ctor_get(x_2766, 1);
lean_dec(x_2772);
x_2773 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2767);
x_2774 = !lean_is_exclusive(x_2773);
if (x_2774 == 0)
{
lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; uint8_t x_2792; 
x_2775 = lean_ctor_get(x_2773, 0);
x_2776 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2775);
x_2777 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2777, 0, x_2775);
lean_ctor_set(x_2777, 1, x_2776);
x_2778 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2779 = lean_array_push(x_2778, x_2757);
x_2780 = lean_box(2);
x_2781 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2782 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2782, 0, x_2780);
lean_ctor_set(x_2782, 1, x_2781);
lean_ctor_set(x_2782, 2, x_2779);
x_2783 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2784 = lean_array_push(x_2783, x_2782);
x_2785 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2786 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2786, 0, x_2780);
lean_ctor_set(x_2786, 1, x_2785);
lean_ctor_set(x_2786, 2, x_2784);
x_2787 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2775);
x_2788 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2788, 0, x_2775);
lean_ctor_set(x_2788, 1, x_2787);
x_2789 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2775);
x_2790 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2790, 0, x_2775);
lean_ctor_set(x_2790, 1, x_2789);
lean_inc(x_14);
x_2791 = lean_array_push(x_2783, x_14);
x_2792 = !lean_is_exclusive(x_14);
if (x_2792 == 0)
{
lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; lean_object* x_2802; lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; uint8_t x_2820; lean_object* x_2821; 
x_2793 = lean_ctor_get(x_14, 2);
lean_dec(x_2793);
x_2794 = lean_ctor_get(x_14, 1);
lean_dec(x_2794);
x_2795 = lean_ctor_get(x_14, 0);
lean_dec(x_2795);
lean_ctor_set(x_14, 2, x_2791);
lean_ctor_set(x_14, 1, x_2785);
lean_ctor_set(x_14, 0, x_2780);
x_2796 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2797 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2797, 0, x_2775);
lean_ctor_set(x_2797, 1, x_2796);
x_2798 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2799 = lean_array_push(x_2798, x_2790);
x_2800 = lean_array_push(x_2799, x_14);
x_2801 = lean_array_push(x_2800, x_2797);
x_2802 = lean_array_push(x_2801, x_2771);
x_2803 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2804 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2804, 0, x_2780);
lean_ctor_set(x_2804, 1, x_2803);
lean_ctor_set(x_2804, 2, x_2802);
x_2805 = lean_array_push(x_2783, x_2804);
x_2806 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2806, 0, x_2780);
lean_ctor_set(x_2806, 1, x_2785);
lean_ctor_set(x_2806, 2, x_2805);
x_2807 = lean_array_push(x_2783, x_2806);
x_2808 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2809 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2809, 0, x_2780);
lean_ctor_set(x_2809, 1, x_2808);
lean_ctor_set(x_2809, 2, x_2807);
x_2810 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2811 = lean_array_push(x_2810, x_2777);
x_2812 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2813 = lean_array_push(x_2811, x_2812);
x_2814 = lean_array_push(x_2813, x_2786);
x_2815 = lean_array_push(x_2814, x_2812);
x_2816 = lean_array_push(x_2815, x_2788);
x_2817 = lean_array_push(x_2816, x_2809);
x_2818 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2819 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2819, 0, x_2780);
lean_ctor_set(x_2819, 1, x_2818);
lean_ctor_set(x_2819, 2, x_2817);
x_2820 = 1;
x_2821 = lean_box(x_2820);
lean_ctor_set(x_2766, 1, x_2821);
lean_ctor_set(x_2766, 0, x_2819);
lean_ctor_set(x_2773, 0, x_2765);
return x_2773;
}
else
{
lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; uint8_t x_2847; lean_object* x_2848; 
lean_dec(x_14);
x_2822 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2822, 0, x_2780);
lean_ctor_set(x_2822, 1, x_2785);
lean_ctor_set(x_2822, 2, x_2791);
x_2823 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2824 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2824, 0, x_2775);
lean_ctor_set(x_2824, 1, x_2823);
x_2825 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2826 = lean_array_push(x_2825, x_2790);
x_2827 = lean_array_push(x_2826, x_2822);
x_2828 = lean_array_push(x_2827, x_2824);
x_2829 = lean_array_push(x_2828, x_2771);
x_2830 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2831 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2831, 0, x_2780);
lean_ctor_set(x_2831, 1, x_2830);
lean_ctor_set(x_2831, 2, x_2829);
x_2832 = lean_array_push(x_2783, x_2831);
x_2833 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2833, 0, x_2780);
lean_ctor_set(x_2833, 1, x_2785);
lean_ctor_set(x_2833, 2, x_2832);
x_2834 = lean_array_push(x_2783, x_2833);
x_2835 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2836 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2836, 0, x_2780);
lean_ctor_set(x_2836, 1, x_2835);
lean_ctor_set(x_2836, 2, x_2834);
x_2837 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2838 = lean_array_push(x_2837, x_2777);
x_2839 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2840 = lean_array_push(x_2838, x_2839);
x_2841 = lean_array_push(x_2840, x_2786);
x_2842 = lean_array_push(x_2841, x_2839);
x_2843 = lean_array_push(x_2842, x_2788);
x_2844 = lean_array_push(x_2843, x_2836);
x_2845 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2846 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2846, 0, x_2780);
lean_ctor_set(x_2846, 1, x_2845);
lean_ctor_set(x_2846, 2, x_2844);
x_2847 = 1;
x_2848 = lean_box(x_2847);
lean_ctor_set(x_2766, 1, x_2848);
lean_ctor_set(x_2766, 0, x_2846);
lean_ctor_set(x_2773, 0, x_2765);
return x_2773;
}
}
else
{
lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; uint8_t x_2893; lean_object* x_2894; lean_object* x_2895; 
x_2849 = lean_ctor_get(x_2773, 0);
x_2850 = lean_ctor_get(x_2773, 1);
lean_inc(x_2850);
lean_inc(x_2849);
lean_dec(x_2773);
x_2851 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2849);
x_2852 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2852, 0, x_2849);
lean_ctor_set(x_2852, 1, x_2851);
x_2853 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2854 = lean_array_push(x_2853, x_2757);
x_2855 = lean_box(2);
x_2856 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2857 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2857, 0, x_2855);
lean_ctor_set(x_2857, 1, x_2856);
lean_ctor_set(x_2857, 2, x_2854);
x_2858 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2859 = lean_array_push(x_2858, x_2857);
x_2860 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2861 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2861, 0, x_2855);
lean_ctor_set(x_2861, 1, x_2860);
lean_ctor_set(x_2861, 2, x_2859);
x_2862 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2849);
x_2863 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2863, 0, x_2849);
lean_ctor_set(x_2863, 1, x_2862);
x_2864 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2849);
x_2865 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2865, 0, x_2849);
lean_ctor_set(x_2865, 1, x_2864);
lean_inc(x_14);
x_2866 = lean_array_push(x_2858, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2867 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2867 = lean_box(0);
}
if (lean_is_scalar(x_2867)) {
 x_2868 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2868 = x_2867;
}
lean_ctor_set(x_2868, 0, x_2855);
lean_ctor_set(x_2868, 1, x_2860);
lean_ctor_set(x_2868, 2, x_2866);
x_2869 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2870 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2870, 0, x_2849);
lean_ctor_set(x_2870, 1, x_2869);
x_2871 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2872 = lean_array_push(x_2871, x_2865);
x_2873 = lean_array_push(x_2872, x_2868);
x_2874 = lean_array_push(x_2873, x_2870);
x_2875 = lean_array_push(x_2874, x_2771);
x_2876 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2877 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2877, 0, x_2855);
lean_ctor_set(x_2877, 1, x_2876);
lean_ctor_set(x_2877, 2, x_2875);
x_2878 = lean_array_push(x_2858, x_2877);
x_2879 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2879, 0, x_2855);
lean_ctor_set(x_2879, 1, x_2860);
lean_ctor_set(x_2879, 2, x_2878);
x_2880 = lean_array_push(x_2858, x_2879);
x_2881 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2882 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2882, 0, x_2855);
lean_ctor_set(x_2882, 1, x_2881);
lean_ctor_set(x_2882, 2, x_2880);
x_2883 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2884 = lean_array_push(x_2883, x_2852);
x_2885 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2886 = lean_array_push(x_2884, x_2885);
x_2887 = lean_array_push(x_2886, x_2861);
x_2888 = lean_array_push(x_2887, x_2885);
x_2889 = lean_array_push(x_2888, x_2863);
x_2890 = lean_array_push(x_2889, x_2882);
x_2891 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2892 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2892, 0, x_2855);
lean_ctor_set(x_2892, 1, x_2891);
lean_ctor_set(x_2892, 2, x_2890);
x_2893 = 1;
x_2894 = lean_box(x_2893);
lean_ctor_set(x_2766, 1, x_2894);
lean_ctor_set(x_2766, 0, x_2892);
x_2895 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2895, 0, x_2765);
lean_ctor_set(x_2895, 1, x_2850);
return x_2895;
}
}
else
{
lean_object* x_2896; lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; uint8_t x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; 
x_2896 = lean_ctor_get(x_2766, 0);
lean_inc(x_2896);
lean_dec(x_2766);
x_2897 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2767);
x_2898 = lean_ctor_get(x_2897, 0);
lean_inc(x_2898);
x_2899 = lean_ctor_get(x_2897, 1);
lean_inc(x_2899);
if (lean_is_exclusive(x_2897)) {
 lean_ctor_release(x_2897, 0);
 lean_ctor_release(x_2897, 1);
 x_2900 = x_2897;
} else {
 lean_dec_ref(x_2897);
 x_2900 = lean_box(0);
}
x_2901 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2898);
x_2902 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2902, 0, x_2898);
lean_ctor_set(x_2902, 1, x_2901);
x_2903 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2904 = lean_array_push(x_2903, x_2757);
x_2905 = lean_box(2);
x_2906 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2907 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2907, 0, x_2905);
lean_ctor_set(x_2907, 1, x_2906);
lean_ctor_set(x_2907, 2, x_2904);
x_2908 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2909 = lean_array_push(x_2908, x_2907);
x_2910 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2911 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2911, 0, x_2905);
lean_ctor_set(x_2911, 1, x_2910);
lean_ctor_set(x_2911, 2, x_2909);
x_2912 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2898);
x_2913 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2913, 0, x_2898);
lean_ctor_set(x_2913, 1, x_2912);
x_2914 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2898);
x_2915 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2915, 0, x_2898);
lean_ctor_set(x_2915, 1, x_2914);
lean_inc(x_14);
x_2916 = lean_array_push(x_2908, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2917 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2917 = lean_box(0);
}
if (lean_is_scalar(x_2917)) {
 x_2918 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2918 = x_2917;
}
lean_ctor_set(x_2918, 0, x_2905);
lean_ctor_set(x_2918, 1, x_2910);
lean_ctor_set(x_2918, 2, x_2916);
x_2919 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2920 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2920, 0, x_2898);
lean_ctor_set(x_2920, 1, x_2919);
x_2921 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2922 = lean_array_push(x_2921, x_2915);
x_2923 = lean_array_push(x_2922, x_2918);
x_2924 = lean_array_push(x_2923, x_2920);
x_2925 = lean_array_push(x_2924, x_2896);
x_2926 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2927 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2927, 0, x_2905);
lean_ctor_set(x_2927, 1, x_2926);
lean_ctor_set(x_2927, 2, x_2925);
x_2928 = lean_array_push(x_2908, x_2927);
x_2929 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2929, 0, x_2905);
lean_ctor_set(x_2929, 1, x_2910);
lean_ctor_set(x_2929, 2, x_2928);
x_2930 = lean_array_push(x_2908, x_2929);
x_2931 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2932 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2932, 0, x_2905);
lean_ctor_set(x_2932, 1, x_2931);
lean_ctor_set(x_2932, 2, x_2930);
x_2933 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2934 = lean_array_push(x_2933, x_2902);
x_2935 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2936 = lean_array_push(x_2934, x_2935);
x_2937 = lean_array_push(x_2936, x_2911);
x_2938 = lean_array_push(x_2937, x_2935);
x_2939 = lean_array_push(x_2938, x_2913);
x_2940 = lean_array_push(x_2939, x_2932);
x_2941 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2942 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2942, 0, x_2905);
lean_ctor_set(x_2942, 1, x_2941);
lean_ctor_set(x_2942, 2, x_2940);
x_2943 = 1;
x_2944 = lean_box(x_2943);
x_2945 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2945, 0, x_2942);
lean_ctor_set(x_2945, 1, x_2944);
lean_ctor_set(x_2765, 1, x_2945);
if (lean_is_scalar(x_2900)) {
 x_2946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2946 = x_2900;
}
lean_ctor_set(x_2946, 0, x_2765);
lean_ctor_set(x_2946, 1, x_2899);
return x_2946;
}
}
else
{
lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; uint8_t x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; 
x_2947 = lean_ctor_get(x_2765, 0);
lean_inc(x_2947);
lean_dec(x_2765);
x_2948 = lean_ctor_get(x_2766, 0);
lean_inc(x_2948);
if (lean_is_exclusive(x_2766)) {
 lean_ctor_release(x_2766, 0);
 lean_ctor_release(x_2766, 1);
 x_2949 = x_2766;
} else {
 lean_dec_ref(x_2766);
 x_2949 = lean_box(0);
}
x_2950 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_2767);
x_2951 = lean_ctor_get(x_2950, 0);
lean_inc(x_2951);
x_2952 = lean_ctor_get(x_2950, 1);
lean_inc(x_2952);
if (lean_is_exclusive(x_2950)) {
 lean_ctor_release(x_2950, 0);
 lean_ctor_release(x_2950, 1);
 x_2953 = x_2950;
} else {
 lean_dec_ref(x_2950);
 x_2953 = lean_box(0);
}
x_2954 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_2951);
x_2955 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2955, 0, x_2951);
lean_ctor_set(x_2955, 1, x_2954);
x_2956 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_2957 = lean_array_push(x_2956, x_2757);
x_2958 = lean_box(2);
x_2959 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_2960 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2960, 0, x_2958);
lean_ctor_set(x_2960, 1, x_2959);
lean_ctor_set(x_2960, 2, x_2957);
x_2961 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_2962 = lean_array_push(x_2961, x_2960);
x_2963 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_2964 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2964, 0, x_2958);
lean_ctor_set(x_2964, 1, x_2963);
lean_ctor_set(x_2964, 2, x_2962);
x_2965 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_2951);
x_2966 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2966, 0, x_2951);
lean_ctor_set(x_2966, 1, x_2965);
x_2967 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_2951);
x_2968 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2968, 0, x_2951);
lean_ctor_set(x_2968, 1, x_2967);
lean_inc(x_14);
x_2969 = lean_array_push(x_2961, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_2970 = x_14;
} else {
 lean_dec_ref(x_14);
 x_2970 = lean_box(0);
}
if (lean_is_scalar(x_2970)) {
 x_2971 = lean_alloc_ctor(1, 3, 0);
} else {
 x_2971 = x_2970;
}
lean_ctor_set(x_2971, 0, x_2958);
lean_ctor_set(x_2971, 1, x_2963);
lean_ctor_set(x_2971, 2, x_2969);
x_2972 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_2973 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_2973, 0, x_2951);
lean_ctor_set(x_2973, 1, x_2972);
x_2974 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_2975 = lean_array_push(x_2974, x_2968);
x_2976 = lean_array_push(x_2975, x_2971);
x_2977 = lean_array_push(x_2976, x_2973);
x_2978 = lean_array_push(x_2977, x_2948);
x_2979 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_2980 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2980, 0, x_2958);
lean_ctor_set(x_2980, 1, x_2979);
lean_ctor_set(x_2980, 2, x_2978);
x_2981 = lean_array_push(x_2961, x_2980);
x_2982 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2982, 0, x_2958);
lean_ctor_set(x_2982, 1, x_2963);
lean_ctor_set(x_2982, 2, x_2981);
x_2983 = lean_array_push(x_2961, x_2982);
x_2984 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_2985 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2985, 0, x_2958);
lean_ctor_set(x_2985, 1, x_2984);
lean_ctor_set(x_2985, 2, x_2983);
x_2986 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_2987 = lean_array_push(x_2986, x_2955);
x_2988 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_2989 = lean_array_push(x_2987, x_2988);
x_2990 = lean_array_push(x_2989, x_2964);
x_2991 = lean_array_push(x_2990, x_2988);
x_2992 = lean_array_push(x_2991, x_2966);
x_2993 = lean_array_push(x_2992, x_2985);
x_2994 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_2995 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2995, 0, x_2958);
lean_ctor_set(x_2995, 1, x_2994);
lean_ctor_set(x_2995, 2, x_2993);
x_2996 = 1;
x_2997 = lean_box(x_2996);
if (lean_is_scalar(x_2949)) {
 x_2998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2998 = x_2949;
}
lean_ctor_set(x_2998, 0, x_2995);
lean_ctor_set(x_2998, 1, x_2997);
x_2999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2999, 0, x_2947);
lean_ctor_set(x_2999, 1, x_2998);
if (lean_is_scalar(x_2953)) {
 x_3000 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3000 = x_2953;
}
lean_ctor_set(x_3000, 0, x_2999);
lean_ctor_set(x_3000, 1, x_2952);
return x_3000;
}
}
}
else
{
lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; lean_object* x_3012; uint8_t x_3013; 
lean_dec(x_228);
lean_dec(x_227);
lean_inc(x_5);
lean_inc(x_14);
x_3001 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_3002 = lean_ctor_get(x_3001, 0);
lean_inc(x_3002);
x_3003 = lean_ctor_get(x_3001, 1);
lean_inc(x_3003);
lean_dec(x_3001);
x_3004 = lean_unsigned_to_nat(1u);
x_3005 = lean_nat_add(x_3, x_3004);
lean_dec(x_3);
lean_inc(x_14);
x_3006 = l_Lean_mkHole(x_14);
lean_inc(x_3002);
x_3007 = l_Lean_Elab_Term_mkExplicitBinder(x_3002, x_3006);
x_3008 = lean_array_push(x_4, x_3007);
lean_inc(x_5);
x_3009 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3005, x_3008, x_5, x_3003);
x_3010 = lean_ctor_get(x_3009, 0);
lean_inc(x_3010);
x_3011 = lean_ctor_get(x_3010, 1);
lean_inc(x_3011);
x_3012 = lean_ctor_get(x_3009, 1);
lean_inc(x_3012);
lean_dec(x_3009);
x_3013 = !lean_is_exclusive(x_3010);
if (x_3013 == 0)
{
lean_object* x_3014; uint8_t x_3015; 
x_3014 = lean_ctor_get(x_3010, 1);
lean_dec(x_3014);
x_3015 = !lean_is_exclusive(x_3011);
if (x_3015 == 0)
{
lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; uint8_t x_3019; 
x_3016 = lean_ctor_get(x_3011, 0);
x_3017 = lean_ctor_get(x_3011, 1);
lean_dec(x_3017);
x_3018 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3012);
x_3019 = !lean_is_exclusive(x_3018);
if (x_3019 == 0)
{
lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; uint8_t x_3037; 
x_3020 = lean_ctor_get(x_3018, 0);
x_3021 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3020);
x_3022 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3022, 0, x_3020);
lean_ctor_set(x_3022, 1, x_3021);
x_3023 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3024 = lean_array_push(x_3023, x_3002);
x_3025 = lean_box(2);
x_3026 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3027 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3027, 0, x_3025);
lean_ctor_set(x_3027, 1, x_3026);
lean_ctor_set(x_3027, 2, x_3024);
x_3028 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3029 = lean_array_push(x_3028, x_3027);
x_3030 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3031 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3031, 0, x_3025);
lean_ctor_set(x_3031, 1, x_3030);
lean_ctor_set(x_3031, 2, x_3029);
x_3032 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3020);
x_3033 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3033, 0, x_3020);
lean_ctor_set(x_3033, 1, x_3032);
x_3034 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3020);
x_3035 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3035, 0, x_3020);
lean_ctor_set(x_3035, 1, x_3034);
lean_inc(x_14);
x_3036 = lean_array_push(x_3028, x_14);
x_3037 = !lean_is_exclusive(x_14);
if (x_3037 == 0)
{
lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; lean_object* x_3063; lean_object* x_3064; uint8_t x_3065; lean_object* x_3066; 
x_3038 = lean_ctor_get(x_14, 2);
lean_dec(x_3038);
x_3039 = lean_ctor_get(x_14, 1);
lean_dec(x_3039);
x_3040 = lean_ctor_get(x_14, 0);
lean_dec(x_3040);
lean_ctor_set(x_14, 2, x_3036);
lean_ctor_set(x_14, 1, x_3030);
lean_ctor_set(x_14, 0, x_3025);
x_3041 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3042 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3042, 0, x_3020);
lean_ctor_set(x_3042, 1, x_3041);
x_3043 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3044 = lean_array_push(x_3043, x_3035);
x_3045 = lean_array_push(x_3044, x_14);
x_3046 = lean_array_push(x_3045, x_3042);
x_3047 = lean_array_push(x_3046, x_3016);
x_3048 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3049 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3049, 0, x_3025);
lean_ctor_set(x_3049, 1, x_3048);
lean_ctor_set(x_3049, 2, x_3047);
x_3050 = lean_array_push(x_3028, x_3049);
x_3051 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3051, 0, x_3025);
lean_ctor_set(x_3051, 1, x_3030);
lean_ctor_set(x_3051, 2, x_3050);
x_3052 = lean_array_push(x_3028, x_3051);
x_3053 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3054 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3054, 0, x_3025);
lean_ctor_set(x_3054, 1, x_3053);
lean_ctor_set(x_3054, 2, x_3052);
x_3055 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3056 = lean_array_push(x_3055, x_3022);
x_3057 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3058 = lean_array_push(x_3056, x_3057);
x_3059 = lean_array_push(x_3058, x_3031);
x_3060 = lean_array_push(x_3059, x_3057);
x_3061 = lean_array_push(x_3060, x_3033);
x_3062 = lean_array_push(x_3061, x_3054);
x_3063 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3064 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3064, 0, x_3025);
lean_ctor_set(x_3064, 1, x_3063);
lean_ctor_set(x_3064, 2, x_3062);
x_3065 = 1;
x_3066 = lean_box(x_3065);
lean_ctor_set(x_3011, 1, x_3066);
lean_ctor_set(x_3011, 0, x_3064);
lean_ctor_set(x_3018, 0, x_3010);
return x_3018;
}
else
{
lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; lean_object* x_3086; lean_object* x_3087; lean_object* x_3088; lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; uint8_t x_3092; lean_object* x_3093; 
lean_dec(x_14);
x_3067 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3067, 0, x_3025);
lean_ctor_set(x_3067, 1, x_3030);
lean_ctor_set(x_3067, 2, x_3036);
x_3068 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3069 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3069, 0, x_3020);
lean_ctor_set(x_3069, 1, x_3068);
x_3070 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3071 = lean_array_push(x_3070, x_3035);
x_3072 = lean_array_push(x_3071, x_3067);
x_3073 = lean_array_push(x_3072, x_3069);
x_3074 = lean_array_push(x_3073, x_3016);
x_3075 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3076 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3076, 0, x_3025);
lean_ctor_set(x_3076, 1, x_3075);
lean_ctor_set(x_3076, 2, x_3074);
x_3077 = lean_array_push(x_3028, x_3076);
x_3078 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3078, 0, x_3025);
lean_ctor_set(x_3078, 1, x_3030);
lean_ctor_set(x_3078, 2, x_3077);
x_3079 = lean_array_push(x_3028, x_3078);
x_3080 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3081 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3081, 0, x_3025);
lean_ctor_set(x_3081, 1, x_3080);
lean_ctor_set(x_3081, 2, x_3079);
x_3082 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3083 = lean_array_push(x_3082, x_3022);
x_3084 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3085 = lean_array_push(x_3083, x_3084);
x_3086 = lean_array_push(x_3085, x_3031);
x_3087 = lean_array_push(x_3086, x_3084);
x_3088 = lean_array_push(x_3087, x_3033);
x_3089 = lean_array_push(x_3088, x_3081);
x_3090 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3091 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3091, 0, x_3025);
lean_ctor_set(x_3091, 1, x_3090);
lean_ctor_set(x_3091, 2, x_3089);
x_3092 = 1;
x_3093 = lean_box(x_3092);
lean_ctor_set(x_3011, 1, x_3093);
lean_ctor_set(x_3011, 0, x_3091);
lean_ctor_set(x_3018, 0, x_3010);
return x_3018;
}
}
else
{
lean_object* x_3094; lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; lean_object* x_3134; lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; uint8_t x_3138; lean_object* x_3139; lean_object* x_3140; 
x_3094 = lean_ctor_get(x_3018, 0);
x_3095 = lean_ctor_get(x_3018, 1);
lean_inc(x_3095);
lean_inc(x_3094);
lean_dec(x_3018);
x_3096 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3094);
x_3097 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3097, 0, x_3094);
lean_ctor_set(x_3097, 1, x_3096);
x_3098 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3099 = lean_array_push(x_3098, x_3002);
x_3100 = lean_box(2);
x_3101 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3102, 0, x_3100);
lean_ctor_set(x_3102, 1, x_3101);
lean_ctor_set(x_3102, 2, x_3099);
x_3103 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3104 = lean_array_push(x_3103, x_3102);
x_3105 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3106, 0, x_3100);
lean_ctor_set(x_3106, 1, x_3105);
lean_ctor_set(x_3106, 2, x_3104);
x_3107 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3094);
x_3108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3108, 0, x_3094);
lean_ctor_set(x_3108, 1, x_3107);
x_3109 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3094);
x_3110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3110, 0, x_3094);
lean_ctor_set(x_3110, 1, x_3109);
lean_inc(x_14);
x_3111 = lean_array_push(x_3103, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_3112 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3112 = lean_box(0);
}
if (lean_is_scalar(x_3112)) {
 x_3113 = lean_alloc_ctor(1, 3, 0);
} else {
 x_3113 = x_3112;
}
lean_ctor_set(x_3113, 0, x_3100);
lean_ctor_set(x_3113, 1, x_3105);
lean_ctor_set(x_3113, 2, x_3111);
x_3114 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3115, 0, x_3094);
lean_ctor_set(x_3115, 1, x_3114);
x_3116 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3117 = lean_array_push(x_3116, x_3110);
x_3118 = lean_array_push(x_3117, x_3113);
x_3119 = lean_array_push(x_3118, x_3115);
x_3120 = lean_array_push(x_3119, x_3016);
x_3121 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3122, 0, x_3100);
lean_ctor_set(x_3122, 1, x_3121);
lean_ctor_set(x_3122, 2, x_3120);
x_3123 = lean_array_push(x_3103, x_3122);
x_3124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3124, 0, x_3100);
lean_ctor_set(x_3124, 1, x_3105);
lean_ctor_set(x_3124, 2, x_3123);
x_3125 = lean_array_push(x_3103, x_3124);
x_3126 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3127, 0, x_3100);
lean_ctor_set(x_3127, 1, x_3126);
lean_ctor_set(x_3127, 2, x_3125);
x_3128 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3129 = lean_array_push(x_3128, x_3097);
x_3130 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3131 = lean_array_push(x_3129, x_3130);
x_3132 = lean_array_push(x_3131, x_3106);
x_3133 = lean_array_push(x_3132, x_3130);
x_3134 = lean_array_push(x_3133, x_3108);
x_3135 = lean_array_push(x_3134, x_3127);
x_3136 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3137, 0, x_3100);
lean_ctor_set(x_3137, 1, x_3136);
lean_ctor_set(x_3137, 2, x_3135);
x_3138 = 1;
x_3139 = lean_box(x_3138);
lean_ctor_set(x_3011, 1, x_3139);
lean_ctor_set(x_3011, 0, x_3137);
x_3140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3140, 0, x_3010);
lean_ctor_set(x_3140, 1, x_3095);
return x_3140;
}
}
else
{
lean_object* x_3141; lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; lean_object* x_3182; lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; uint8_t x_3188; lean_object* x_3189; lean_object* x_3190; lean_object* x_3191; 
x_3141 = lean_ctor_get(x_3011, 0);
lean_inc(x_3141);
lean_dec(x_3011);
x_3142 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3012);
x_3143 = lean_ctor_get(x_3142, 0);
lean_inc(x_3143);
x_3144 = lean_ctor_get(x_3142, 1);
lean_inc(x_3144);
if (lean_is_exclusive(x_3142)) {
 lean_ctor_release(x_3142, 0);
 lean_ctor_release(x_3142, 1);
 x_3145 = x_3142;
} else {
 lean_dec_ref(x_3142);
 x_3145 = lean_box(0);
}
x_3146 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3143);
x_3147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3147, 0, x_3143);
lean_ctor_set(x_3147, 1, x_3146);
x_3148 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3149 = lean_array_push(x_3148, x_3002);
x_3150 = lean_box(2);
x_3151 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3152, 0, x_3150);
lean_ctor_set(x_3152, 1, x_3151);
lean_ctor_set(x_3152, 2, x_3149);
x_3153 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3154 = lean_array_push(x_3153, x_3152);
x_3155 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3156, 0, x_3150);
lean_ctor_set(x_3156, 1, x_3155);
lean_ctor_set(x_3156, 2, x_3154);
x_3157 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3143);
x_3158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3158, 0, x_3143);
lean_ctor_set(x_3158, 1, x_3157);
x_3159 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3143);
x_3160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3160, 0, x_3143);
lean_ctor_set(x_3160, 1, x_3159);
lean_inc(x_14);
x_3161 = lean_array_push(x_3153, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_3162 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3162 = lean_box(0);
}
if (lean_is_scalar(x_3162)) {
 x_3163 = lean_alloc_ctor(1, 3, 0);
} else {
 x_3163 = x_3162;
}
lean_ctor_set(x_3163, 0, x_3150);
lean_ctor_set(x_3163, 1, x_3155);
lean_ctor_set(x_3163, 2, x_3161);
x_3164 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3165, 0, x_3143);
lean_ctor_set(x_3165, 1, x_3164);
x_3166 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3167 = lean_array_push(x_3166, x_3160);
x_3168 = lean_array_push(x_3167, x_3163);
x_3169 = lean_array_push(x_3168, x_3165);
x_3170 = lean_array_push(x_3169, x_3141);
x_3171 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3172, 0, x_3150);
lean_ctor_set(x_3172, 1, x_3171);
lean_ctor_set(x_3172, 2, x_3170);
x_3173 = lean_array_push(x_3153, x_3172);
x_3174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3174, 0, x_3150);
lean_ctor_set(x_3174, 1, x_3155);
lean_ctor_set(x_3174, 2, x_3173);
x_3175 = lean_array_push(x_3153, x_3174);
x_3176 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3177, 0, x_3150);
lean_ctor_set(x_3177, 1, x_3176);
lean_ctor_set(x_3177, 2, x_3175);
x_3178 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3179 = lean_array_push(x_3178, x_3147);
x_3180 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3181 = lean_array_push(x_3179, x_3180);
x_3182 = lean_array_push(x_3181, x_3156);
x_3183 = lean_array_push(x_3182, x_3180);
x_3184 = lean_array_push(x_3183, x_3158);
x_3185 = lean_array_push(x_3184, x_3177);
x_3186 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3187, 0, x_3150);
lean_ctor_set(x_3187, 1, x_3186);
lean_ctor_set(x_3187, 2, x_3185);
x_3188 = 1;
x_3189 = lean_box(x_3188);
x_3190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3190, 0, x_3187);
lean_ctor_set(x_3190, 1, x_3189);
lean_ctor_set(x_3010, 1, x_3190);
if (lean_is_scalar(x_3145)) {
 x_3191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3191 = x_3145;
}
lean_ctor_set(x_3191, 0, x_3010);
lean_ctor_set(x_3191, 1, x_3144);
return x_3191;
}
}
else
{
lean_object* x_3192; lean_object* x_3193; lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; lean_object* x_3203; lean_object* x_3204; lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; lean_object* x_3229; lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; uint8_t x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; 
x_3192 = lean_ctor_get(x_3010, 0);
lean_inc(x_3192);
lean_dec(x_3010);
x_3193 = lean_ctor_get(x_3011, 0);
lean_inc(x_3193);
if (lean_is_exclusive(x_3011)) {
 lean_ctor_release(x_3011, 0);
 lean_ctor_release(x_3011, 1);
 x_3194 = x_3011;
} else {
 lean_dec_ref(x_3011);
 x_3194 = lean_box(0);
}
x_3195 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3012);
x_3196 = lean_ctor_get(x_3195, 0);
lean_inc(x_3196);
x_3197 = lean_ctor_get(x_3195, 1);
lean_inc(x_3197);
if (lean_is_exclusive(x_3195)) {
 lean_ctor_release(x_3195, 0);
 lean_ctor_release(x_3195, 1);
 x_3198 = x_3195;
} else {
 lean_dec_ref(x_3195);
 x_3198 = lean_box(0);
}
x_3199 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3196);
x_3200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3200, 0, x_3196);
lean_ctor_set(x_3200, 1, x_3199);
x_3201 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3202 = lean_array_push(x_3201, x_3002);
x_3203 = lean_box(2);
x_3204 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3205, 0, x_3203);
lean_ctor_set(x_3205, 1, x_3204);
lean_ctor_set(x_3205, 2, x_3202);
x_3206 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3207 = lean_array_push(x_3206, x_3205);
x_3208 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3209, 0, x_3203);
lean_ctor_set(x_3209, 1, x_3208);
lean_ctor_set(x_3209, 2, x_3207);
x_3210 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3196);
x_3211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3211, 0, x_3196);
lean_ctor_set(x_3211, 1, x_3210);
x_3212 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3196);
x_3213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3213, 0, x_3196);
lean_ctor_set(x_3213, 1, x_3212);
lean_inc(x_14);
x_3214 = lean_array_push(x_3206, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_3215 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3215 = lean_box(0);
}
if (lean_is_scalar(x_3215)) {
 x_3216 = lean_alloc_ctor(1, 3, 0);
} else {
 x_3216 = x_3215;
}
lean_ctor_set(x_3216, 0, x_3203);
lean_ctor_set(x_3216, 1, x_3208);
lean_ctor_set(x_3216, 2, x_3214);
x_3217 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3218, 0, x_3196);
lean_ctor_set(x_3218, 1, x_3217);
x_3219 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3220 = lean_array_push(x_3219, x_3213);
x_3221 = lean_array_push(x_3220, x_3216);
x_3222 = lean_array_push(x_3221, x_3218);
x_3223 = lean_array_push(x_3222, x_3193);
x_3224 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3225 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3225, 0, x_3203);
lean_ctor_set(x_3225, 1, x_3224);
lean_ctor_set(x_3225, 2, x_3223);
x_3226 = lean_array_push(x_3206, x_3225);
x_3227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3227, 0, x_3203);
lean_ctor_set(x_3227, 1, x_3208);
lean_ctor_set(x_3227, 2, x_3226);
x_3228 = lean_array_push(x_3206, x_3227);
x_3229 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3230, 0, x_3203);
lean_ctor_set(x_3230, 1, x_3229);
lean_ctor_set(x_3230, 2, x_3228);
x_3231 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3232 = lean_array_push(x_3231, x_3200);
x_3233 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3234 = lean_array_push(x_3232, x_3233);
x_3235 = lean_array_push(x_3234, x_3209);
x_3236 = lean_array_push(x_3235, x_3233);
x_3237 = lean_array_push(x_3236, x_3211);
x_3238 = lean_array_push(x_3237, x_3230);
x_3239 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3240, 0, x_3203);
lean_ctor_set(x_3240, 1, x_3239);
lean_ctor_set(x_3240, 2, x_3238);
x_3241 = 1;
x_3242 = lean_box(x_3241);
if (lean_is_scalar(x_3194)) {
 x_3243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3243 = x_3194;
}
lean_ctor_set(x_3243, 0, x_3240);
lean_ctor_set(x_3243, 1, x_3242);
x_3244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3244, 0, x_3192);
lean_ctor_set(x_3244, 1, x_3243);
if (lean_is_scalar(x_3198)) {
 x_3245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3245 = x_3198;
}
lean_ctor_set(x_3245, 0, x_3244);
lean_ctor_set(x_3245, 1, x_3197);
return x_3245;
}
}
}
else
{
lean_object* x_3246; lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; lean_object* x_3250; lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; lean_object* x_3256; lean_object* x_3257; uint8_t x_3258; 
lean_dec(x_227);
lean_inc(x_5);
lean_inc(x_14);
x_3246 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_3247 = lean_ctor_get(x_3246, 0);
lean_inc(x_3247);
x_3248 = lean_ctor_get(x_3246, 1);
lean_inc(x_3248);
lean_dec(x_3246);
x_3249 = lean_unsigned_to_nat(1u);
x_3250 = lean_nat_add(x_3, x_3249);
lean_dec(x_3);
lean_inc(x_14);
x_3251 = l_Lean_mkHole(x_14);
lean_inc(x_3247);
x_3252 = l_Lean_Elab_Term_mkExplicitBinder(x_3247, x_3251);
x_3253 = lean_array_push(x_4, x_3252);
lean_inc(x_5);
x_3254 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3250, x_3253, x_5, x_3248);
x_3255 = lean_ctor_get(x_3254, 0);
lean_inc(x_3255);
x_3256 = lean_ctor_get(x_3255, 1);
lean_inc(x_3256);
x_3257 = lean_ctor_get(x_3254, 1);
lean_inc(x_3257);
lean_dec(x_3254);
x_3258 = !lean_is_exclusive(x_3255);
if (x_3258 == 0)
{
lean_object* x_3259; uint8_t x_3260; 
x_3259 = lean_ctor_get(x_3255, 1);
lean_dec(x_3259);
x_3260 = !lean_is_exclusive(x_3256);
if (x_3260 == 0)
{
lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; uint8_t x_3264; 
x_3261 = lean_ctor_get(x_3256, 0);
x_3262 = lean_ctor_get(x_3256, 1);
lean_dec(x_3262);
x_3263 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3257);
x_3264 = !lean_is_exclusive(x_3263);
if (x_3264 == 0)
{
lean_object* x_3265; lean_object* x_3266; lean_object* x_3267; lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; lean_object* x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; uint8_t x_3282; 
x_3265 = lean_ctor_get(x_3263, 0);
x_3266 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3265);
x_3267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3267, 0, x_3265);
lean_ctor_set(x_3267, 1, x_3266);
x_3268 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3269 = lean_array_push(x_3268, x_3247);
x_3270 = lean_box(2);
x_3271 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3272 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3272, 0, x_3270);
lean_ctor_set(x_3272, 1, x_3271);
lean_ctor_set(x_3272, 2, x_3269);
x_3273 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3274 = lean_array_push(x_3273, x_3272);
x_3275 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3276 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3276, 0, x_3270);
lean_ctor_set(x_3276, 1, x_3275);
lean_ctor_set(x_3276, 2, x_3274);
x_3277 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3265);
x_3278 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3278, 0, x_3265);
lean_ctor_set(x_3278, 1, x_3277);
x_3279 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3265);
x_3280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3280, 0, x_3265);
lean_ctor_set(x_3280, 1, x_3279);
lean_inc(x_14);
x_3281 = lean_array_push(x_3273, x_14);
x_3282 = !lean_is_exclusive(x_14);
if (x_3282 == 0)
{
lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; lean_object* x_3306; lean_object* x_3307; lean_object* x_3308; lean_object* x_3309; uint8_t x_3310; lean_object* x_3311; 
x_3283 = lean_ctor_get(x_14, 2);
lean_dec(x_3283);
x_3284 = lean_ctor_get(x_14, 1);
lean_dec(x_3284);
x_3285 = lean_ctor_get(x_14, 0);
lean_dec(x_3285);
lean_ctor_set(x_14, 2, x_3281);
lean_ctor_set(x_14, 1, x_3275);
lean_ctor_set(x_14, 0, x_3270);
x_3286 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3287, 0, x_3265);
lean_ctor_set(x_3287, 1, x_3286);
x_3288 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3289 = lean_array_push(x_3288, x_3280);
x_3290 = lean_array_push(x_3289, x_14);
x_3291 = lean_array_push(x_3290, x_3287);
x_3292 = lean_array_push(x_3291, x_3261);
x_3293 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3294, 0, x_3270);
lean_ctor_set(x_3294, 1, x_3293);
lean_ctor_set(x_3294, 2, x_3292);
x_3295 = lean_array_push(x_3273, x_3294);
x_3296 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3296, 0, x_3270);
lean_ctor_set(x_3296, 1, x_3275);
lean_ctor_set(x_3296, 2, x_3295);
x_3297 = lean_array_push(x_3273, x_3296);
x_3298 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3299, 0, x_3270);
lean_ctor_set(x_3299, 1, x_3298);
lean_ctor_set(x_3299, 2, x_3297);
x_3300 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3301 = lean_array_push(x_3300, x_3267);
x_3302 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3303 = lean_array_push(x_3301, x_3302);
x_3304 = lean_array_push(x_3303, x_3276);
x_3305 = lean_array_push(x_3304, x_3302);
x_3306 = lean_array_push(x_3305, x_3278);
x_3307 = lean_array_push(x_3306, x_3299);
x_3308 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3309, 0, x_3270);
lean_ctor_set(x_3309, 1, x_3308);
lean_ctor_set(x_3309, 2, x_3307);
x_3310 = 1;
x_3311 = lean_box(x_3310);
lean_ctor_set(x_3256, 1, x_3311);
lean_ctor_set(x_3256, 0, x_3309);
lean_ctor_set(x_3263, 0, x_3255);
return x_3263;
}
else
{
lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; lean_object* x_3315; lean_object* x_3316; lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; uint8_t x_3337; lean_object* x_3338; 
lean_dec(x_14);
x_3312 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3312, 0, x_3270);
lean_ctor_set(x_3312, 1, x_3275);
lean_ctor_set(x_3312, 2, x_3281);
x_3313 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3314, 0, x_3265);
lean_ctor_set(x_3314, 1, x_3313);
x_3315 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3316 = lean_array_push(x_3315, x_3280);
x_3317 = lean_array_push(x_3316, x_3312);
x_3318 = lean_array_push(x_3317, x_3314);
x_3319 = lean_array_push(x_3318, x_3261);
x_3320 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3321 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3321, 0, x_3270);
lean_ctor_set(x_3321, 1, x_3320);
lean_ctor_set(x_3321, 2, x_3319);
x_3322 = lean_array_push(x_3273, x_3321);
x_3323 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3323, 0, x_3270);
lean_ctor_set(x_3323, 1, x_3275);
lean_ctor_set(x_3323, 2, x_3322);
x_3324 = lean_array_push(x_3273, x_3323);
x_3325 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3326 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3326, 0, x_3270);
lean_ctor_set(x_3326, 1, x_3325);
lean_ctor_set(x_3326, 2, x_3324);
x_3327 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3328 = lean_array_push(x_3327, x_3267);
x_3329 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3330 = lean_array_push(x_3328, x_3329);
x_3331 = lean_array_push(x_3330, x_3276);
x_3332 = lean_array_push(x_3331, x_3329);
x_3333 = lean_array_push(x_3332, x_3278);
x_3334 = lean_array_push(x_3333, x_3326);
x_3335 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3336 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3336, 0, x_3270);
lean_ctor_set(x_3336, 1, x_3335);
lean_ctor_set(x_3336, 2, x_3334);
x_3337 = 1;
x_3338 = lean_box(x_3337);
lean_ctor_set(x_3256, 1, x_3338);
lean_ctor_set(x_3256, 0, x_3336);
lean_ctor_set(x_3263, 0, x_3255);
return x_3263;
}
}
else
{
lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; lean_object* x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; lean_object* x_3366; lean_object* x_3367; lean_object* x_3368; lean_object* x_3369; lean_object* x_3370; lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; lean_object* x_3374; lean_object* x_3375; lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; lean_object* x_3382; uint8_t x_3383; lean_object* x_3384; lean_object* x_3385; 
x_3339 = lean_ctor_get(x_3263, 0);
x_3340 = lean_ctor_get(x_3263, 1);
lean_inc(x_3340);
lean_inc(x_3339);
lean_dec(x_3263);
x_3341 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3339);
x_3342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3342, 0, x_3339);
lean_ctor_set(x_3342, 1, x_3341);
x_3343 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3344 = lean_array_push(x_3343, x_3247);
x_3345 = lean_box(2);
x_3346 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3347, 0, x_3345);
lean_ctor_set(x_3347, 1, x_3346);
lean_ctor_set(x_3347, 2, x_3344);
x_3348 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3349 = lean_array_push(x_3348, x_3347);
x_3350 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3351 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3351, 0, x_3345);
lean_ctor_set(x_3351, 1, x_3350);
lean_ctor_set(x_3351, 2, x_3349);
x_3352 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3339);
x_3353 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3353, 0, x_3339);
lean_ctor_set(x_3353, 1, x_3352);
x_3354 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3339);
x_3355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3355, 0, x_3339);
lean_ctor_set(x_3355, 1, x_3354);
lean_inc(x_14);
x_3356 = lean_array_push(x_3348, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_3357 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3357 = lean_box(0);
}
if (lean_is_scalar(x_3357)) {
 x_3358 = lean_alloc_ctor(1, 3, 0);
} else {
 x_3358 = x_3357;
}
lean_ctor_set(x_3358, 0, x_3345);
lean_ctor_set(x_3358, 1, x_3350);
lean_ctor_set(x_3358, 2, x_3356);
x_3359 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3360, 0, x_3339);
lean_ctor_set(x_3360, 1, x_3359);
x_3361 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3362 = lean_array_push(x_3361, x_3355);
x_3363 = lean_array_push(x_3362, x_3358);
x_3364 = lean_array_push(x_3363, x_3360);
x_3365 = lean_array_push(x_3364, x_3261);
x_3366 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3367 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3367, 0, x_3345);
lean_ctor_set(x_3367, 1, x_3366);
lean_ctor_set(x_3367, 2, x_3365);
x_3368 = lean_array_push(x_3348, x_3367);
x_3369 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3369, 0, x_3345);
lean_ctor_set(x_3369, 1, x_3350);
lean_ctor_set(x_3369, 2, x_3368);
x_3370 = lean_array_push(x_3348, x_3369);
x_3371 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3372, 0, x_3345);
lean_ctor_set(x_3372, 1, x_3371);
lean_ctor_set(x_3372, 2, x_3370);
x_3373 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3374 = lean_array_push(x_3373, x_3342);
x_3375 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3376 = lean_array_push(x_3374, x_3375);
x_3377 = lean_array_push(x_3376, x_3351);
x_3378 = lean_array_push(x_3377, x_3375);
x_3379 = lean_array_push(x_3378, x_3353);
x_3380 = lean_array_push(x_3379, x_3372);
x_3381 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3382 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3382, 0, x_3345);
lean_ctor_set(x_3382, 1, x_3381);
lean_ctor_set(x_3382, 2, x_3380);
x_3383 = 1;
x_3384 = lean_box(x_3383);
lean_ctor_set(x_3256, 1, x_3384);
lean_ctor_set(x_3256, 0, x_3382);
x_3385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3385, 0, x_3255);
lean_ctor_set(x_3385, 1, x_3340);
return x_3385;
}
}
else
{
lean_object* x_3386; lean_object* x_3387; lean_object* x_3388; lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; lean_object* x_3429; lean_object* x_3430; lean_object* x_3431; lean_object* x_3432; uint8_t x_3433; lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; 
x_3386 = lean_ctor_get(x_3256, 0);
lean_inc(x_3386);
lean_dec(x_3256);
x_3387 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3257);
x_3388 = lean_ctor_get(x_3387, 0);
lean_inc(x_3388);
x_3389 = lean_ctor_get(x_3387, 1);
lean_inc(x_3389);
if (lean_is_exclusive(x_3387)) {
 lean_ctor_release(x_3387, 0);
 lean_ctor_release(x_3387, 1);
 x_3390 = x_3387;
} else {
 lean_dec_ref(x_3387);
 x_3390 = lean_box(0);
}
x_3391 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3388);
x_3392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3392, 0, x_3388);
lean_ctor_set(x_3392, 1, x_3391);
x_3393 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3394 = lean_array_push(x_3393, x_3247);
x_3395 = lean_box(2);
x_3396 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3397 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3397, 0, x_3395);
lean_ctor_set(x_3397, 1, x_3396);
lean_ctor_set(x_3397, 2, x_3394);
x_3398 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3399 = lean_array_push(x_3398, x_3397);
x_3400 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3401 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3401, 0, x_3395);
lean_ctor_set(x_3401, 1, x_3400);
lean_ctor_set(x_3401, 2, x_3399);
x_3402 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3388);
x_3403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3403, 0, x_3388);
lean_ctor_set(x_3403, 1, x_3402);
x_3404 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3388);
x_3405 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3405, 0, x_3388);
lean_ctor_set(x_3405, 1, x_3404);
lean_inc(x_14);
x_3406 = lean_array_push(x_3398, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_3407 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3407 = lean_box(0);
}
if (lean_is_scalar(x_3407)) {
 x_3408 = lean_alloc_ctor(1, 3, 0);
} else {
 x_3408 = x_3407;
}
lean_ctor_set(x_3408, 0, x_3395);
lean_ctor_set(x_3408, 1, x_3400);
lean_ctor_set(x_3408, 2, x_3406);
x_3409 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3410, 0, x_3388);
lean_ctor_set(x_3410, 1, x_3409);
x_3411 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3412 = lean_array_push(x_3411, x_3405);
x_3413 = lean_array_push(x_3412, x_3408);
x_3414 = lean_array_push(x_3413, x_3410);
x_3415 = lean_array_push(x_3414, x_3386);
x_3416 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3417 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3417, 0, x_3395);
lean_ctor_set(x_3417, 1, x_3416);
lean_ctor_set(x_3417, 2, x_3415);
x_3418 = lean_array_push(x_3398, x_3417);
x_3419 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3419, 0, x_3395);
lean_ctor_set(x_3419, 1, x_3400);
lean_ctor_set(x_3419, 2, x_3418);
x_3420 = lean_array_push(x_3398, x_3419);
x_3421 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3422 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3422, 0, x_3395);
lean_ctor_set(x_3422, 1, x_3421);
lean_ctor_set(x_3422, 2, x_3420);
x_3423 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3424 = lean_array_push(x_3423, x_3392);
x_3425 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3426 = lean_array_push(x_3424, x_3425);
x_3427 = lean_array_push(x_3426, x_3401);
x_3428 = lean_array_push(x_3427, x_3425);
x_3429 = lean_array_push(x_3428, x_3403);
x_3430 = lean_array_push(x_3429, x_3422);
x_3431 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3432 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3432, 0, x_3395);
lean_ctor_set(x_3432, 1, x_3431);
lean_ctor_set(x_3432, 2, x_3430);
x_3433 = 1;
x_3434 = lean_box(x_3433);
x_3435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3435, 0, x_3432);
lean_ctor_set(x_3435, 1, x_3434);
lean_ctor_set(x_3255, 1, x_3435);
if (lean_is_scalar(x_3390)) {
 x_3436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3436 = x_3390;
}
lean_ctor_set(x_3436, 0, x_3255);
lean_ctor_set(x_3436, 1, x_3389);
return x_3436;
}
}
else
{
lean_object* x_3437; lean_object* x_3438; lean_object* x_3439; lean_object* x_3440; lean_object* x_3441; lean_object* x_3442; lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; lean_object* x_3448; lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; lean_object* x_3454; lean_object* x_3455; lean_object* x_3456; lean_object* x_3457; lean_object* x_3458; lean_object* x_3459; lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; lean_object* x_3470; lean_object* x_3471; lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; uint8_t x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; 
x_3437 = lean_ctor_get(x_3255, 0);
lean_inc(x_3437);
lean_dec(x_3255);
x_3438 = lean_ctor_get(x_3256, 0);
lean_inc(x_3438);
if (lean_is_exclusive(x_3256)) {
 lean_ctor_release(x_3256, 0);
 lean_ctor_release(x_3256, 1);
 x_3439 = x_3256;
} else {
 lean_dec_ref(x_3256);
 x_3439 = lean_box(0);
}
x_3440 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3257);
x_3441 = lean_ctor_get(x_3440, 0);
lean_inc(x_3441);
x_3442 = lean_ctor_get(x_3440, 1);
lean_inc(x_3442);
if (lean_is_exclusive(x_3440)) {
 lean_ctor_release(x_3440, 0);
 lean_ctor_release(x_3440, 1);
 x_3443 = x_3440;
} else {
 lean_dec_ref(x_3440);
 x_3443 = lean_box(0);
}
x_3444 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3441);
x_3445 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3445, 0, x_3441);
lean_ctor_set(x_3445, 1, x_3444);
x_3446 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3447 = lean_array_push(x_3446, x_3247);
x_3448 = lean_box(2);
x_3449 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3450, 0, x_3448);
lean_ctor_set(x_3450, 1, x_3449);
lean_ctor_set(x_3450, 2, x_3447);
x_3451 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3452 = lean_array_push(x_3451, x_3450);
x_3453 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3454 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3454, 0, x_3448);
lean_ctor_set(x_3454, 1, x_3453);
lean_ctor_set(x_3454, 2, x_3452);
x_3455 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3441);
x_3456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3456, 0, x_3441);
lean_ctor_set(x_3456, 1, x_3455);
x_3457 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3441);
x_3458 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3458, 0, x_3441);
lean_ctor_set(x_3458, 1, x_3457);
lean_inc(x_14);
x_3459 = lean_array_push(x_3451, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_3460 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3460 = lean_box(0);
}
if (lean_is_scalar(x_3460)) {
 x_3461 = lean_alloc_ctor(1, 3, 0);
} else {
 x_3461 = x_3460;
}
lean_ctor_set(x_3461, 0, x_3448);
lean_ctor_set(x_3461, 1, x_3453);
lean_ctor_set(x_3461, 2, x_3459);
x_3462 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3463, 0, x_3441);
lean_ctor_set(x_3463, 1, x_3462);
x_3464 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3465 = lean_array_push(x_3464, x_3458);
x_3466 = lean_array_push(x_3465, x_3461);
x_3467 = lean_array_push(x_3466, x_3463);
x_3468 = lean_array_push(x_3467, x_3438);
x_3469 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3470 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3470, 0, x_3448);
lean_ctor_set(x_3470, 1, x_3469);
lean_ctor_set(x_3470, 2, x_3468);
x_3471 = lean_array_push(x_3451, x_3470);
x_3472 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3472, 0, x_3448);
lean_ctor_set(x_3472, 1, x_3453);
lean_ctor_set(x_3472, 2, x_3471);
x_3473 = lean_array_push(x_3451, x_3472);
x_3474 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3475 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3475, 0, x_3448);
lean_ctor_set(x_3475, 1, x_3474);
lean_ctor_set(x_3475, 2, x_3473);
x_3476 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3477 = lean_array_push(x_3476, x_3445);
x_3478 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3479 = lean_array_push(x_3477, x_3478);
x_3480 = lean_array_push(x_3479, x_3454);
x_3481 = lean_array_push(x_3480, x_3478);
x_3482 = lean_array_push(x_3481, x_3456);
x_3483 = lean_array_push(x_3482, x_3475);
x_3484 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3485 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3485, 0, x_3448);
lean_ctor_set(x_3485, 1, x_3484);
lean_ctor_set(x_3485, 2, x_3483);
x_3486 = 1;
x_3487 = lean_box(x_3486);
if (lean_is_scalar(x_3439)) {
 x_3488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3488 = x_3439;
}
lean_ctor_set(x_3488, 0, x_3485);
lean_ctor_set(x_3488, 1, x_3487);
x_3489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3489, 0, x_3437);
lean_ctor_set(x_3489, 1, x_3488);
if (lean_is_scalar(x_3443)) {
 x_3490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3490 = x_3443;
}
lean_ctor_set(x_3490, 0, x_3489);
lean_ctor_set(x_3490, 1, x_3442);
return x_3490;
}
}
}
case 2:
{
lean_object* x_3491; lean_object* x_3492; lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; lean_object* x_3499; lean_object* x_3500; lean_object* x_3501; lean_object* x_3502; uint8_t x_3503; 
lean_inc(x_5);
lean_inc(x_14);
x_3491 = l_Lean_Elab_Term_mkFreshIdent___at_Lean_Elab_Term_expandFunBinders_loop___spec__1(x_14, x_5, x_6);
x_3492 = lean_ctor_get(x_3491, 0);
lean_inc(x_3492);
x_3493 = lean_ctor_get(x_3491, 1);
lean_inc(x_3493);
lean_dec(x_3491);
x_3494 = lean_unsigned_to_nat(1u);
x_3495 = lean_nat_add(x_3, x_3494);
lean_dec(x_3);
lean_inc(x_14);
x_3496 = l_Lean_mkHole(x_14);
lean_inc(x_3492);
x_3497 = l_Lean_Elab_Term_mkExplicitBinder(x_3492, x_3496);
x_3498 = lean_array_push(x_4, x_3497);
lean_inc(x_5);
x_3499 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3495, x_3498, x_5, x_3493);
x_3500 = lean_ctor_get(x_3499, 0);
lean_inc(x_3500);
x_3501 = lean_ctor_get(x_3500, 1);
lean_inc(x_3501);
x_3502 = lean_ctor_get(x_3499, 1);
lean_inc(x_3502);
lean_dec(x_3499);
x_3503 = !lean_is_exclusive(x_3500);
if (x_3503 == 0)
{
lean_object* x_3504; uint8_t x_3505; 
x_3504 = lean_ctor_get(x_3500, 1);
lean_dec(x_3504);
x_3505 = !lean_is_exclusive(x_3501);
if (x_3505 == 0)
{
lean_object* x_3506; lean_object* x_3507; lean_object* x_3508; uint8_t x_3509; 
x_3506 = lean_ctor_get(x_3501, 0);
x_3507 = lean_ctor_get(x_3501, 1);
lean_dec(x_3507);
x_3508 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3502);
x_3509 = !lean_is_exclusive(x_3508);
if (x_3509 == 0)
{
lean_object* x_3510; lean_object* x_3511; lean_object* x_3512; lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; lean_object* x_3526; uint8_t x_3527; 
x_3510 = lean_ctor_get(x_3508, 0);
x_3511 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3510);
x_3512 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3512, 0, x_3510);
lean_ctor_set(x_3512, 1, x_3511);
x_3513 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3514 = lean_array_push(x_3513, x_3492);
x_3515 = lean_box(2);
x_3516 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3517 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3517, 0, x_3515);
lean_ctor_set(x_3517, 1, x_3516);
lean_ctor_set(x_3517, 2, x_3514);
x_3518 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3519 = lean_array_push(x_3518, x_3517);
x_3520 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3521 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3521, 0, x_3515);
lean_ctor_set(x_3521, 1, x_3520);
lean_ctor_set(x_3521, 2, x_3519);
x_3522 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3510);
x_3523 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3523, 0, x_3510);
lean_ctor_set(x_3523, 1, x_3522);
x_3524 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3510);
x_3525 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3525, 0, x_3510);
lean_ctor_set(x_3525, 1, x_3524);
lean_inc(x_14);
x_3526 = lean_array_push(x_3518, x_14);
x_3527 = !lean_is_exclusive(x_14);
if (x_3527 == 0)
{
lean_object* x_3528; lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; lean_object* x_3541; lean_object* x_3542; lean_object* x_3543; lean_object* x_3544; lean_object* x_3545; lean_object* x_3546; lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; uint8_t x_3554; lean_object* x_3555; 
x_3528 = lean_ctor_get(x_14, 1);
lean_dec(x_3528);
x_3529 = lean_ctor_get(x_14, 0);
lean_dec(x_3529);
x_3530 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3530, 0, x_3515);
lean_ctor_set(x_3530, 1, x_3520);
lean_ctor_set(x_3530, 2, x_3526);
x_3531 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
lean_ctor_set(x_14, 1, x_3531);
lean_ctor_set(x_14, 0, x_3510);
x_3532 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3533 = lean_array_push(x_3532, x_3525);
x_3534 = lean_array_push(x_3533, x_3530);
x_3535 = lean_array_push(x_3534, x_14);
x_3536 = lean_array_push(x_3535, x_3506);
x_3537 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3538 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3538, 0, x_3515);
lean_ctor_set(x_3538, 1, x_3537);
lean_ctor_set(x_3538, 2, x_3536);
x_3539 = lean_array_push(x_3518, x_3538);
x_3540 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3540, 0, x_3515);
lean_ctor_set(x_3540, 1, x_3520);
lean_ctor_set(x_3540, 2, x_3539);
x_3541 = lean_array_push(x_3518, x_3540);
x_3542 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3543 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3543, 0, x_3515);
lean_ctor_set(x_3543, 1, x_3542);
lean_ctor_set(x_3543, 2, x_3541);
x_3544 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3545 = lean_array_push(x_3544, x_3512);
x_3546 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3547 = lean_array_push(x_3545, x_3546);
x_3548 = lean_array_push(x_3547, x_3521);
x_3549 = lean_array_push(x_3548, x_3546);
x_3550 = lean_array_push(x_3549, x_3523);
x_3551 = lean_array_push(x_3550, x_3543);
x_3552 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3553 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3553, 0, x_3515);
lean_ctor_set(x_3553, 1, x_3552);
lean_ctor_set(x_3553, 2, x_3551);
x_3554 = 1;
x_3555 = lean_box(x_3554);
lean_ctor_set(x_3501, 1, x_3555);
lean_ctor_set(x_3501, 0, x_3553);
lean_ctor_set(x_3508, 0, x_3500);
return x_3508;
}
else
{
lean_object* x_3556; lean_object* x_3557; lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; lean_object* x_3573; lean_object* x_3574; lean_object* x_3575; lean_object* x_3576; lean_object* x_3577; lean_object* x_3578; lean_object* x_3579; lean_object* x_3580; uint8_t x_3581; lean_object* x_3582; 
lean_dec(x_14);
x_3556 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3556, 0, x_3515);
lean_ctor_set(x_3556, 1, x_3520);
lean_ctor_set(x_3556, 2, x_3526);
x_3557 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_3558 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3558, 0, x_3510);
lean_ctor_set(x_3558, 1, x_3557);
x_3559 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3560 = lean_array_push(x_3559, x_3525);
x_3561 = lean_array_push(x_3560, x_3556);
x_3562 = lean_array_push(x_3561, x_3558);
x_3563 = lean_array_push(x_3562, x_3506);
x_3564 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3565 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3565, 0, x_3515);
lean_ctor_set(x_3565, 1, x_3564);
lean_ctor_set(x_3565, 2, x_3563);
x_3566 = lean_array_push(x_3518, x_3565);
x_3567 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3567, 0, x_3515);
lean_ctor_set(x_3567, 1, x_3520);
lean_ctor_set(x_3567, 2, x_3566);
x_3568 = lean_array_push(x_3518, x_3567);
x_3569 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3570 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3570, 0, x_3515);
lean_ctor_set(x_3570, 1, x_3569);
lean_ctor_set(x_3570, 2, x_3568);
x_3571 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3572 = lean_array_push(x_3571, x_3512);
x_3573 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3574 = lean_array_push(x_3572, x_3573);
x_3575 = lean_array_push(x_3574, x_3521);
x_3576 = lean_array_push(x_3575, x_3573);
x_3577 = lean_array_push(x_3576, x_3523);
x_3578 = lean_array_push(x_3577, x_3570);
x_3579 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3580 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3580, 0, x_3515);
lean_ctor_set(x_3580, 1, x_3579);
lean_ctor_set(x_3580, 2, x_3578);
x_3581 = 1;
x_3582 = lean_box(x_3581);
lean_ctor_set(x_3501, 1, x_3582);
lean_ctor_set(x_3501, 0, x_3580);
lean_ctor_set(x_3508, 0, x_3500);
return x_3508;
}
}
else
{
lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; lean_object* x_3591; lean_object* x_3592; lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; lean_object* x_3599; lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; lean_object* x_3603; lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; lean_object* x_3607; lean_object* x_3608; lean_object* x_3609; lean_object* x_3610; lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; lean_object* x_3614; lean_object* x_3615; lean_object* x_3616; lean_object* x_3617; lean_object* x_3618; lean_object* x_3619; lean_object* x_3620; lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; lean_object* x_3625; lean_object* x_3626; uint8_t x_3627; lean_object* x_3628; lean_object* x_3629; 
x_3583 = lean_ctor_get(x_3508, 0);
x_3584 = lean_ctor_get(x_3508, 1);
lean_inc(x_3584);
lean_inc(x_3583);
lean_dec(x_3508);
x_3585 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3583);
x_3586 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3586, 0, x_3583);
lean_ctor_set(x_3586, 1, x_3585);
x_3587 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3588 = lean_array_push(x_3587, x_3492);
x_3589 = lean_box(2);
x_3590 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3591 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3591, 0, x_3589);
lean_ctor_set(x_3591, 1, x_3590);
lean_ctor_set(x_3591, 2, x_3588);
x_3592 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3593 = lean_array_push(x_3592, x_3591);
x_3594 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3595 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3595, 0, x_3589);
lean_ctor_set(x_3595, 1, x_3594);
lean_ctor_set(x_3595, 2, x_3593);
x_3596 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3583);
x_3597 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3597, 0, x_3583);
lean_ctor_set(x_3597, 1, x_3596);
x_3598 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3583);
x_3599 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3599, 0, x_3583);
lean_ctor_set(x_3599, 1, x_3598);
lean_inc(x_14);
x_3600 = lean_array_push(x_3592, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3601 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3601 = lean_box(0);
}
x_3602 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3602, 0, x_3589);
lean_ctor_set(x_3602, 1, x_3594);
lean_ctor_set(x_3602, 2, x_3600);
x_3603 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
if (lean_is_scalar(x_3601)) {
 x_3604 = lean_alloc_ctor(2, 2, 0);
} else {
 x_3604 = x_3601;
}
lean_ctor_set(x_3604, 0, x_3583);
lean_ctor_set(x_3604, 1, x_3603);
x_3605 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3606 = lean_array_push(x_3605, x_3599);
x_3607 = lean_array_push(x_3606, x_3602);
x_3608 = lean_array_push(x_3607, x_3604);
x_3609 = lean_array_push(x_3608, x_3506);
x_3610 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3611 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3611, 0, x_3589);
lean_ctor_set(x_3611, 1, x_3610);
lean_ctor_set(x_3611, 2, x_3609);
x_3612 = lean_array_push(x_3592, x_3611);
x_3613 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3613, 0, x_3589);
lean_ctor_set(x_3613, 1, x_3594);
lean_ctor_set(x_3613, 2, x_3612);
x_3614 = lean_array_push(x_3592, x_3613);
x_3615 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3616 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3616, 0, x_3589);
lean_ctor_set(x_3616, 1, x_3615);
lean_ctor_set(x_3616, 2, x_3614);
x_3617 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3618 = lean_array_push(x_3617, x_3586);
x_3619 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3620 = lean_array_push(x_3618, x_3619);
x_3621 = lean_array_push(x_3620, x_3595);
x_3622 = lean_array_push(x_3621, x_3619);
x_3623 = lean_array_push(x_3622, x_3597);
x_3624 = lean_array_push(x_3623, x_3616);
x_3625 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3626 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3626, 0, x_3589);
lean_ctor_set(x_3626, 1, x_3625);
lean_ctor_set(x_3626, 2, x_3624);
x_3627 = 1;
x_3628 = lean_box(x_3627);
lean_ctor_set(x_3501, 1, x_3628);
lean_ctor_set(x_3501, 0, x_3626);
x_3629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3629, 0, x_3500);
lean_ctor_set(x_3629, 1, x_3584);
return x_3629;
}
}
else
{
lean_object* x_3630; lean_object* x_3631; lean_object* x_3632; lean_object* x_3633; lean_object* x_3634; lean_object* x_3635; lean_object* x_3636; lean_object* x_3637; lean_object* x_3638; lean_object* x_3639; lean_object* x_3640; lean_object* x_3641; lean_object* x_3642; lean_object* x_3643; lean_object* x_3644; lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; lean_object* x_3648; lean_object* x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; lean_object* x_3662; lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; lean_object* x_3667; lean_object* x_3668; lean_object* x_3669; lean_object* x_3670; lean_object* x_3671; lean_object* x_3672; lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; uint8_t x_3677; lean_object* x_3678; lean_object* x_3679; lean_object* x_3680; 
x_3630 = lean_ctor_get(x_3501, 0);
lean_inc(x_3630);
lean_dec(x_3501);
x_3631 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3502);
x_3632 = lean_ctor_get(x_3631, 0);
lean_inc(x_3632);
x_3633 = lean_ctor_get(x_3631, 1);
lean_inc(x_3633);
if (lean_is_exclusive(x_3631)) {
 lean_ctor_release(x_3631, 0);
 lean_ctor_release(x_3631, 1);
 x_3634 = x_3631;
} else {
 lean_dec_ref(x_3631);
 x_3634 = lean_box(0);
}
x_3635 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3632);
x_3636 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3636, 0, x_3632);
lean_ctor_set(x_3636, 1, x_3635);
x_3637 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3638 = lean_array_push(x_3637, x_3492);
x_3639 = lean_box(2);
x_3640 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3641 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3641, 0, x_3639);
lean_ctor_set(x_3641, 1, x_3640);
lean_ctor_set(x_3641, 2, x_3638);
x_3642 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3643 = lean_array_push(x_3642, x_3641);
x_3644 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3645 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3645, 0, x_3639);
lean_ctor_set(x_3645, 1, x_3644);
lean_ctor_set(x_3645, 2, x_3643);
x_3646 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3632);
x_3647 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3647, 0, x_3632);
lean_ctor_set(x_3647, 1, x_3646);
x_3648 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3632);
x_3649 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3649, 0, x_3632);
lean_ctor_set(x_3649, 1, x_3648);
lean_inc(x_14);
x_3650 = lean_array_push(x_3642, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3651 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3651 = lean_box(0);
}
x_3652 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3652, 0, x_3639);
lean_ctor_set(x_3652, 1, x_3644);
lean_ctor_set(x_3652, 2, x_3650);
x_3653 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
if (lean_is_scalar(x_3651)) {
 x_3654 = lean_alloc_ctor(2, 2, 0);
} else {
 x_3654 = x_3651;
}
lean_ctor_set(x_3654, 0, x_3632);
lean_ctor_set(x_3654, 1, x_3653);
x_3655 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3656 = lean_array_push(x_3655, x_3649);
x_3657 = lean_array_push(x_3656, x_3652);
x_3658 = lean_array_push(x_3657, x_3654);
x_3659 = lean_array_push(x_3658, x_3630);
x_3660 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3661 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3661, 0, x_3639);
lean_ctor_set(x_3661, 1, x_3660);
lean_ctor_set(x_3661, 2, x_3659);
x_3662 = lean_array_push(x_3642, x_3661);
x_3663 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3663, 0, x_3639);
lean_ctor_set(x_3663, 1, x_3644);
lean_ctor_set(x_3663, 2, x_3662);
x_3664 = lean_array_push(x_3642, x_3663);
x_3665 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3666 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3666, 0, x_3639);
lean_ctor_set(x_3666, 1, x_3665);
lean_ctor_set(x_3666, 2, x_3664);
x_3667 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3668 = lean_array_push(x_3667, x_3636);
x_3669 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3670 = lean_array_push(x_3668, x_3669);
x_3671 = lean_array_push(x_3670, x_3645);
x_3672 = lean_array_push(x_3671, x_3669);
x_3673 = lean_array_push(x_3672, x_3647);
x_3674 = lean_array_push(x_3673, x_3666);
x_3675 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3676 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3676, 0, x_3639);
lean_ctor_set(x_3676, 1, x_3675);
lean_ctor_set(x_3676, 2, x_3674);
x_3677 = 1;
x_3678 = lean_box(x_3677);
x_3679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3679, 0, x_3676);
lean_ctor_set(x_3679, 1, x_3678);
lean_ctor_set(x_3500, 1, x_3679);
if (lean_is_scalar(x_3634)) {
 x_3680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3680 = x_3634;
}
lean_ctor_set(x_3680, 0, x_3500);
lean_ctor_set(x_3680, 1, x_3633);
return x_3680;
}
}
else
{
lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; lean_object* x_3695; lean_object* x_3696; lean_object* x_3697; lean_object* x_3698; lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; lean_object* x_3702; lean_object* x_3703; lean_object* x_3704; lean_object* x_3705; lean_object* x_3706; lean_object* x_3707; lean_object* x_3708; lean_object* x_3709; lean_object* x_3710; lean_object* x_3711; lean_object* x_3712; lean_object* x_3713; lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; lean_object* x_3717; lean_object* x_3718; lean_object* x_3719; lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; uint8_t x_3730; lean_object* x_3731; lean_object* x_3732; lean_object* x_3733; lean_object* x_3734; 
x_3681 = lean_ctor_get(x_3500, 0);
lean_inc(x_3681);
lean_dec(x_3500);
x_3682 = lean_ctor_get(x_3501, 0);
lean_inc(x_3682);
if (lean_is_exclusive(x_3501)) {
 lean_ctor_release(x_3501, 0);
 lean_ctor_release(x_3501, 1);
 x_3683 = x_3501;
} else {
 lean_dec_ref(x_3501);
 x_3683 = lean_box(0);
}
x_3684 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_3502);
x_3685 = lean_ctor_get(x_3684, 0);
lean_inc(x_3685);
x_3686 = lean_ctor_get(x_3684, 1);
lean_inc(x_3686);
if (lean_is_exclusive(x_3684)) {
 lean_ctor_release(x_3684, 0);
 lean_ctor_release(x_3684, 1);
 x_3687 = x_3684;
} else {
 lean_dec_ref(x_3684);
 x_3687 = lean_box(0);
}
x_3688 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_3685);
x_3689 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3689, 0, x_3685);
lean_ctor_set(x_3689, 1, x_3688);
x_3690 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_3691 = lean_array_push(x_3690, x_3492);
x_3692 = lean_box(2);
x_3693 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_3694 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3694, 0, x_3692);
lean_ctor_set(x_3694, 1, x_3693);
lean_ctor_set(x_3694, 2, x_3691);
x_3695 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_3696 = lean_array_push(x_3695, x_3694);
x_3697 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_3698 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3698, 0, x_3692);
lean_ctor_set(x_3698, 1, x_3697);
lean_ctor_set(x_3698, 2, x_3696);
x_3699 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_3685);
x_3700 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3700, 0, x_3685);
lean_ctor_set(x_3700, 1, x_3699);
x_3701 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_3685);
x_3702 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3702, 0, x_3685);
lean_ctor_set(x_3702, 1, x_3701);
lean_inc(x_14);
x_3703 = lean_array_push(x_3695, x_14);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_3704 = x_14;
} else {
 lean_dec_ref(x_14);
 x_3704 = lean_box(0);
}
x_3705 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3705, 0, x_3692);
lean_ctor_set(x_3705, 1, x_3697);
lean_ctor_set(x_3705, 2, x_3703);
x_3706 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
if (lean_is_scalar(x_3704)) {
 x_3707 = lean_alloc_ctor(2, 2, 0);
} else {
 x_3707 = x_3704;
}
lean_ctor_set(x_3707, 0, x_3685);
lean_ctor_set(x_3707, 1, x_3706);
x_3708 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_3709 = lean_array_push(x_3708, x_3702);
x_3710 = lean_array_push(x_3709, x_3705);
x_3711 = lean_array_push(x_3710, x_3707);
x_3712 = lean_array_push(x_3711, x_3682);
x_3713 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_3714 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3714, 0, x_3692);
lean_ctor_set(x_3714, 1, x_3713);
lean_ctor_set(x_3714, 2, x_3712);
x_3715 = lean_array_push(x_3695, x_3714);
x_3716 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3716, 0, x_3692);
lean_ctor_set(x_3716, 1, x_3697);
lean_ctor_set(x_3716, 2, x_3715);
x_3717 = lean_array_push(x_3695, x_3716);
x_3718 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_3719 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3719, 0, x_3692);
lean_ctor_set(x_3719, 1, x_3718);
lean_ctor_set(x_3719, 2, x_3717);
x_3720 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_3721 = lean_array_push(x_3720, x_3689);
x_3722 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_3723 = lean_array_push(x_3721, x_3722);
x_3724 = lean_array_push(x_3723, x_3698);
x_3725 = lean_array_push(x_3724, x_3722);
x_3726 = lean_array_push(x_3725, x_3700);
x_3727 = lean_array_push(x_3726, x_3719);
x_3728 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_3729 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_3729, 0, x_3692);
lean_ctor_set(x_3729, 1, x_3728);
lean_ctor_set(x_3729, 2, x_3727);
x_3730 = 1;
x_3731 = lean_box(x_3730);
if (lean_is_scalar(x_3683)) {
 x_3732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3732 = x_3683;
}
lean_ctor_set(x_3732, 0, x_3729);
lean_ctor_set(x_3732, 1, x_3731);
x_3733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3733, 0, x_3681);
lean_ctor_set(x_3733, 1, x_3732);
if (lean_is_scalar(x_3687)) {
 x_3734 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3734 = x_3687;
}
lean_ctor_set(x_3734, 0, x_3733);
lean_ctor_set(x_3734, 1, x_3686);
return x_3734;
}
}
default: 
{
lean_object* x_3735; lean_object* x_3736; lean_object* x_3737; lean_object* x_3738; lean_object* x_3739; 
lean_inc(x_14);
x_3735 = l_Lean_mkHole(x_14);
x_3736 = lean_unsigned_to_nat(1u);
x_3737 = lean_nat_add(x_3, x_3736);
lean_dec(x_3);
x_3738 = l_Lean_Elab_Term_mkExplicitBinder(x_14, x_3735);
x_3739 = lean_array_push(x_4, x_3738);
x_3 = x_3737;
x_4 = x_3739;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandFunBinders_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg___boxed), 2, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_3, x_4, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_1, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_15 = l_Lean_Elab_Term_elabType(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_16, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_mkFreshFVarId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(x_8, x_9, x_10, x_11, x_12, x_13, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = l_Lean_mkFVar(x_21);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_inc(x_23);
x_25 = lean_array_push(x_24, x_23);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_3);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
x_29 = l_Lean_Syntax_getId(x_28);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
lean_inc(x_16);
x_31 = lean_local_ctx_mk_local_decl(x_3, x_21, x_29, x_16, x_30);
x_32 = lean_box(0);
lean_inc(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_box(0);
x_35 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_23);
lean_inc(x_28);
x_36 = l_Lean_Elab_Term_addTermInfo(x_28, x_23, x_32, x_33, x_34, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_12, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_12, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_12, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_12, 7);
lean_inc(x_45);
x_46 = l_Lean_replaceRef(x_28, x_41);
lean_dec(x_41);
lean_dec(x_28);
x_47 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 4, x_42);
lean_ctor_set(x_47, 5, x_43);
lean_ctor_set(x_47, 6, x_44);
lean_ctor_set(x_47, 7, x_45);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_16);
x_48 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(x_23, x_16, x_27, x_8, x_9, x_10, x_11, x_47, x_13, x_37);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 2);
x_54 = lean_ctor_get(x_49, 3);
x_55 = lean_ctor_get(x_49, 1);
lean_dec(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_31);
lean_inc(x_52);
lean_ctor_set(x_49, 1, x_31);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_56 = l_Lean_Meta_isClass_x3f(x_16, x_10, x_11, x_12, x_13, x_50);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_31);
lean_dec(x_23);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_6, x_59);
lean_dec(x_6);
x_61 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_60, x_49, x_8, x_9, x_10, x_11, x_12, x_13, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_49);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_23);
x_65 = lean_array_push(x_53, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_6, x_66);
lean_dec(x_6);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_31);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_54);
x_69 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_11, x_12, x_13, x_62);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_72 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_67, x_68, x_8, x_9, x_10, x_11, x_12, x_13, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_restoreSynthInstanceCache(x_70, x_10, x_11, x_12, x_13, x_74);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = l_Lean_Meta_restoreSynthInstanceCache(x_70, x_10, x_11, x_12, x_13, x_81);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set_tag(x_82, 1);
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_49);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_87 = !lean_is_exclusive(x_56);
if (x_87 == 0)
{
return x_56;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_56, 0);
x_89 = lean_ctor_get(x_56, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_56);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_49, 0);
x_92 = lean_ctor_get(x_49, 2);
x_93 = lean_ctor_get(x_49, 3);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_49);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_31);
lean_inc(x_91);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_31);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_93);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_95 = l_Lean_Meta_isClass_x3f(x_16, x_10, x_11, x_12, x_13, x_50);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_31);
lean_dec(x_23);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_6, x_98);
lean_dec(x_6);
x_100 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_99, x_94, x_8, x_9, x_10, x_11, x_12, x_13, x_97);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_94);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_23);
x_104 = lean_array_push(x_92, x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_6, x_105);
lean_dec(x_6);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_31);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_93);
x_108 = l_Lean_Meta_saveAndResetSynthInstanceCache___rarg(x_11, x_12, x_13, x_101);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_111 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_7, x_106, x_107, x_8, x_9, x_10, x_11, x_12, x_13, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Meta_restoreSynthInstanceCache(x_109, x_10, x_11, x_12, x_13, x_113);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
lean_dec(x_111);
x_120 = l_Lean_Meta_restoreSynthInstanceCache(x_109, x_10, x_11, x_12, x_13, x_119);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_124 = lean_ctor_get(x_95, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_95, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_126 = x_95;
} else {
 lean_dec_ref(x_95);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_128 = !lean_is_exclusive(x_48);
if (x_128 == 0)
{
return x_48;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_48, 0);
x_130 = lean_ctor_get(x_48, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_48);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_132 = !lean_is_exclusive(x_36);
if (x_132 == 0)
{
return x_36;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_36, 0);
x_134 = lean_ctor_get(x_36, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_36);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
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
x_136 = !lean_is_exclusive(x_15);
if (x_136 == 0)
{
return x_15;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_15, 0);
x_138 = lean_ctor_get(x_15, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_15);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lambda__1), 14, 7);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_14);
lean_closure_set(x_20, 5, x_2);
lean_closure_set(x_20, 6, x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 3);
x_23 = l_Lean_replaceRef(x_17, x_22);
lean_dec(x_22);
lean_dec(x_17);
lean_ctor_set(x_8, 3, x_23);
x_24 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_18, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
x_29 = lean_ctor_get(x_8, 4);
x_30 = lean_ctor_get(x_8, 5);
x_31 = lean_ctor_get(x_8, 6);
x_32 = lean_ctor_get(x_8, 7);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_33 = l_Lean_replaceRef(x_17, x_28);
lean_dec(x_28);
lean_dec(x_17);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
lean_ctor_set(x_34, 7, x_32);
x_35 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_18, x_19, x_20, x_4, x_5, x_6, x_7, x_34, x_9, x_16);
return x_35;
}
}
else
{
uint8_t x_36; 
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
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshFVarId___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
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
x_30 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_26, x_23, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
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
x_34 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_26, x_23, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
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
x_53 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_54 = lean_apply_9(x_3, x_53, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFunBinders___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabFunBinders___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("group");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letRecDecl");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2;
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
x_8 = l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__3;
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
lean_object* x_1; 
x_1 = lean_mk_string("whereDecls");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letrec");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rec");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letRecDecls");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_expandWhereDecls___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandWhereDecls___lambda__2), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Array_sequenceMap___at___aux__Init__NotationExtra______macroRules___xabterm_x25_x5b___x7c___x5d_xbb__1___spec__1(x_11, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_3, x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
lean_inc(x_20);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Term_expandWhereDecls___closed__6;
lean_inc(x_20);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_26 = lean_array_push(x_25, x_22);
x_27 = lean_array_push(x_26, x_24);
x_28 = lean_box(2);
x_29 = l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2;
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
x_31 = l_Lean_Elab_Term_expandWhereDecls___closed__9;
x_32 = l_Lean_Syntax_SepArray_ofElems(x_31, x_17);
lean_dec(x_17);
x_33 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_34 = l_Array_append___rarg(x_33, x_32);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_34);
x_37 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_38 = lean_array_push(x_37, x_36);
x_39 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_38);
x_41 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_37, x_42);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_28);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_43);
x_45 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_46 = lean_array_push(x_45, x_30);
x_47 = lean_array_push(x_46, x_40);
x_48 = lean_array_push(x_47, x_44);
x_49 = lean_array_push(x_48, x_2);
x_50 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_28);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_18, 0, x_51);
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
lean_inc(x_52);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Term_expandWhereDecls___closed__6;
lean_inc(x_52);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_59 = lean_array_push(x_58, x_55);
x_60 = lean_array_push(x_59, x_57);
x_61 = lean_box(2);
x_62 = l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2;
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_60);
x_64 = l_Lean_Elab_Term_expandWhereDecls___closed__9;
x_65 = l_Lean_Syntax_SepArray_ofElems(x_64, x_17);
lean_dec(x_17);
x_66 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_67 = l_Array_append___rarg(x_66, x_65);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_67);
x_70 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_71 = lean_array_push(x_70, x_69);
x_72 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_71);
x_74 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_52);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_70, x_75);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_79 = lean_array_push(x_78, x_63);
x_80 = lean_array_push(x_79, x_73);
x_81 = lean_array_push(x_80, x_77);
x_82 = lean_array_push(x_81, x_2);
x_83 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_61);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_53);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandWhereDecls___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = l_Lean_Elab_Term_expandFunBinders_loop___closed__4;
lean_inc(x_1);
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
lean_inc(x_2);
x_15 = lean_array_push(x_14, x_2);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = x_18;
x_22 = lean_array_uset(x_10, x_4, x_21);
x_4 = x_20;
x_5 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5;
lean_inc(x_1);
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Lean_Elab_Term_expandFunBinders_loop___closed__4;
x_15 = lean_name_mk_string(x_13, x_14);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
lean_inc(x_2);
x_17 = lean_array_push(x_16, x_2);
x_18 = lean_array_push(x_17, x_11);
x_19 = lean_box(2);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_23 = x_20;
x_24 = lean_array_uset(x_10, x_4, x_23);
x_4 = x_22;
x_5 = x_24;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("basicFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq1");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intro");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11;
x_2 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_15);
lean_ctor_set(x_5, 2, x_12);
lean_inc(x_5);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_21 = l_Lean_addMacroScope(x_15, x_20, x_12);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_inc(x_5);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_31 = lean_array_push(x_30, x_29);
lean_inc(x_24);
x_32 = lean_array_push(x_31, x_24);
x_33 = lean_box(2);
x_34 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_32);
x_36 = lean_array_push(x_4, x_35);
lean_inc(x_5);
x_37 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_36, x_5, x_27);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
x_44 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_42);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_47 = lean_array_push(x_46, x_24);
x_48 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_53 = lean_array_push(x_52, x_49);
x_54 = lean_array_push(x_53, x_51);
x_55 = lean_array_push(x_54, x_38);
x_56 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_55);
x_58 = lean_array_push(x_30, x_45);
x_59 = lean_array_push(x_58, x_57);
x_60 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_33);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_59);
x_62 = lean_array_push(x_30, x_43);
x_63 = lean_array_push(x_62, x_61);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_33);
lean_ctor_set(x_64, 1, x_34);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_40, 0, x_64);
return x_40;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_65 = lean_ctor_get(x_40, 0);
x_66 = lean_ctor_get(x_40, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_40);
lean_inc(x_65);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_28);
x_68 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_65);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_71 = lean_array_push(x_70, x_24);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_33);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_71);
x_74 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_77 = lean_array_push(x_76, x_73);
x_78 = lean_array_push(x_77, x_75);
x_79 = lean_array_push(x_78, x_38);
x_80 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_33);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_79);
x_82 = lean_array_push(x_30, x_69);
x_83 = lean_array_push(x_82, x_81);
x_84 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_33);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_83);
x_86 = lean_array_push(x_30, x_67);
x_87 = lean_array_push(x_86, x_85);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_33);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_66);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_37, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 1);
lean_inc(x_91);
lean_dec(x_37);
x_92 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_94);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_98 = lean_array_push(x_97, x_24);
x_99 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_33);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_98);
x_101 = lean_array_push(x_30, x_96);
x_102 = lean_array_push(x_101, x_100);
x_103 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15;
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_33);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_102);
x_105 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_108 = lean_array_push(x_107, x_104);
x_109 = lean_array_push(x_108, x_106);
x_110 = lean_array_push(x_109, x_90);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_33);
lean_ctor_set(x_111, 1, x_99);
lean_ctor_set(x_111, 2, x_110);
x_112 = lean_array_push(x_97, x_111);
x_113 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_33);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_112);
lean_ctor_set(x_92, 0, x_114);
return x_92;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_115 = lean_ctor_get(x_92, 0);
x_116 = lean_ctor_get(x_92, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_92);
x_117 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_115);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_120 = lean_array_push(x_119, x_24);
x_121 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_33);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_120);
x_123 = lean_array_push(x_30, x_118);
x_124 = lean_array_push(x_123, x_122);
x_125 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15;
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_33);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_124);
x_127 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_115);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_130 = lean_array_push(x_129, x_126);
x_131 = lean_array_push(x_130, x_128);
x_132 = lean_array_push(x_131, x_90);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_33);
lean_ctor_set(x_133, 1, x_121);
lean_ctor_set(x_133, 2, x_132);
x_134 = lean_array_push(x_119, x_133);
x_135 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_33);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_134);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_116);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
x_140 = lean_ctor_get(x_5, 3);
x_141 = lean_ctor_get(x_5, 4);
x_142 = lean_ctor_get(x_5, 5);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_139);
x_143 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_139);
lean_ctor_set(x_143, 2, x_12);
lean_ctor_set(x_143, 3, x_140);
lean_ctor_set(x_143, 4, x_141);
lean_ctor_set(x_143, 5, x_142);
lean_inc(x_143);
x_144 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_143, x_6);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_148 = l_Lean_addMacroScope(x_139, x_147, x_12);
x_149 = lean_box(0);
x_150 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_151 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_148);
lean_ctor_set(x_151, 3, x_149);
lean_inc(x_143);
x_152 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_143, x_146);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_158 = lean_array_push(x_157, x_156);
lean_inc(x_151);
x_159 = lean_array_push(x_158, x_151);
x_160 = lean_box(2);
x_161 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_159);
x_163 = lean_array_push(x_4, x_162);
lean_inc(x_143);
x_164 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_163, x_143, x_154);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_143, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
lean_inc(x_168);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_155);
x_172 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_168);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_175 = lean_array_push(x_174, x_151);
x_176 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_160);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_175);
x_178 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_181 = lean_array_push(x_180, x_177);
x_182 = lean_array_push(x_181, x_179);
x_183 = lean_array_push(x_182, x_165);
x_184 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_185 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_185, 0, x_160);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_183);
x_186 = lean_array_push(x_157, x_173);
x_187 = lean_array_push(x_186, x_185);
x_188 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_160);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_189, 2, x_187);
x_190 = lean_array_push(x_157, x_171);
x_191 = lean_array_push(x_190, x_189);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_160);
lean_ctor_set(x_192, 1, x_161);
lean_ctor_set(x_192, 2, x_191);
if (lean_is_scalar(x_170)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_170;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_169);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_194 = lean_ctor_get(x_164, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_164, 1);
lean_inc(x_195);
lean_dec(x_164);
x_196 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_143, x_195);
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
x_200 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_197);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_203 = lean_array_push(x_202, x_151);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_160);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_203);
x_206 = lean_array_push(x_157, x_201);
x_207 = lean_array_push(x_206, x_205);
x_208 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15;
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_160);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_207);
x_210 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_197);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_213 = lean_array_push(x_212, x_209);
x_214 = lean_array_push(x_213, x_211);
x_215 = lean_array_push(x_214, x_194);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_160);
lean_ctor_set(x_216, 1, x_204);
lean_ctor_set(x_216, 2, x_215);
x_217 = lean_array_push(x_202, x_216);
x_218 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_219 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_219, 0, x_160);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_217);
if (lean_is_scalar(x_199)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_199;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_198);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_221 = lean_ctor_get(x_6, 0);
x_222 = lean_ctor_get(x_6, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_6);
x_223 = lean_nat_add(x_221, x_9);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_ctor_get(x_5, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_5, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_5, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_5, 4);
lean_inc(x_228);
x_229 = lean_ctor_get(x_5, 5);
lean_inc(x_229);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_230 = x_5;
} else {
 lean_dec_ref(x_5);
 x_230 = lean_box(0);
}
lean_inc(x_221);
lean_inc(x_226);
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 6, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_225);
lean_ctor_set(x_231, 1, x_226);
lean_ctor_set(x_231, 2, x_221);
lean_ctor_set(x_231, 3, x_227);
lean_ctor_set(x_231, 4, x_228);
lean_ctor_set(x_231, 5, x_229);
lean_inc(x_231);
x_232 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_231, x_224);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_236 = l_Lean_addMacroScope(x_226, x_235, x_221);
x_237 = lean_box(0);
x_238 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
x_239 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set(x_239, 2, x_236);
lean_ctor_set(x_239, 3, x_237);
lean_inc(x_231);
x_240 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_231, x_234);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_246 = lean_array_push(x_245, x_244);
lean_inc(x_239);
x_247 = lean_array_push(x_246, x_239);
x_248 = lean_box(2);
x_249 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_250 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_247);
x_251 = lean_array_push(x_4, x_250);
lean_inc(x_231);
x_252 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_10, x_251, x_231, x_242);
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_231, x_254);
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
lean_inc(x_256);
x_259 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_243);
x_260 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_256);
x_261 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_263 = lean_array_push(x_262, x_239);
x_264 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_265 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_265, 0, x_248);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set(x_265, 2, x_263);
x_266 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_256);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_269 = lean_array_push(x_268, x_265);
x_270 = lean_array_push(x_269, x_267);
x_271 = lean_array_push(x_270, x_253);
x_272 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_248);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_271);
x_274 = lean_array_push(x_245, x_261);
x_275 = lean_array_push(x_274, x_273);
x_276 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_248);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set(x_277, 2, x_275);
x_278 = lean_array_push(x_245, x_259);
x_279 = lean_array_push(x_278, x_277);
x_280 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_280, 0, x_248);
lean_ctor_set(x_280, 1, x_249);
lean_ctor_set(x_280, 2, x_279);
if (lean_is_scalar(x_258)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_258;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_257);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_282 = lean_ctor_get(x_252, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_252, 1);
lean_inc(x_283);
lean_dec(x_252);
x_284 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_231, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
x_288 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_285);
x_289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_291 = lean_array_push(x_290, x_239);
x_292 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_293, 0, x_248);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_291);
x_294 = lean_array_push(x_245, x_289);
x_295 = lean_array_push(x_294, x_293);
x_296 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15;
x_297 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_297, 0, x_248);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set(x_297, 2, x_295);
x_298 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
x_299 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_299, 0, x_285);
lean_ctor_set(x_299, 1, x_298);
x_300 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_301 = lean_array_push(x_300, x_297);
x_302 = lean_array_push(x_301, x_299);
x_303 = lean_array_push(x_302, x_282);
x_304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_304, 0, x_248);
lean_ctor_set(x_304, 1, x_292);
lean_ctor_set(x_304, 2, x_303);
x_305 = lean_array_push(x_290, x_304);
x_306 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_307 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_307, 0, x_248);
lean_ctor_set(x_307, 1, x_306);
lean_ctor_set(x_307, 2, x_305);
if (lean_is_scalar(x_287)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_287;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_286);
return x_308;
}
}
}
else
{
if (x_2 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_6);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; size_t x_315; size_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_311);
x_313 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_array_get_size(x_4);
x_315 = lean_usize_of_nat(x_314);
lean_dec(x_314);
x_316 = 0;
x_317 = x_4;
x_318 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_319 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_320 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_318, x_319, x_315, x_316, x_317);
x_321 = x_320;
x_322 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
x_323 = l_Lean_mkSepArray(x_321, x_322);
lean_dec(x_321);
x_324 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_325 = l_Array_append___rarg(x_324, x_323);
x_326 = lean_box(2);
x_327 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
lean_ctor_set(x_328, 2, x_325);
x_329 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_311);
lean_ctor_set(x_330, 1, x_329);
x_331 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_332 = lean_array_push(x_331, x_313);
x_333 = lean_array_push(x_332, x_319);
x_334 = lean_array_push(x_333, x_328);
x_335 = lean_array_push(x_334, x_319);
x_336 = lean_array_push(x_335, x_330);
x_337 = lean_array_push(x_336, x_1);
x_338 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_326);
lean_ctor_set(x_339, 1, x_338);
lean_ctor_set(x_339, 2, x_337);
lean_ctor_set(x_309, 0, x_339);
return x_309;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; size_t x_345; size_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_340 = lean_ctor_get(x_309, 0);
x_341 = lean_ctor_get(x_309, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_309);
x_342 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_340);
x_343 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_array_get_size(x_4);
x_345 = lean_usize_of_nat(x_344);
lean_dec(x_344);
x_346 = 0;
x_347 = x_4;
x_348 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_349 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_350 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_348, x_349, x_345, x_346, x_347);
x_351 = x_350;
x_352 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
x_353 = l_Lean_mkSepArray(x_351, x_352);
lean_dec(x_351);
x_354 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_355 = l_Array_append___rarg(x_354, x_353);
x_356 = lean_box(2);
x_357 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_358 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set(x_358, 2, x_355);
x_359 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
x_360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_360, 0, x_340);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_362 = lean_array_push(x_361, x_343);
x_363 = lean_array_push(x_362, x_349);
x_364 = lean_array_push(x_363, x_358);
x_365 = lean_array_push(x_364, x_349);
x_366 = lean_array_push(x_365, x_360);
x_367 = lean_array_push(x_366, x_1);
x_368 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_369 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_369, 0, x_356);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_369, 2, x_367);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_341);
return x_370;
}
}
else
{
lean_object* x_371; uint8_t x_372; 
x_371 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_6);
x_372 = !lean_is_exclusive(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; size_t x_377; size_t x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_373 = lean_ctor_get(x_371, 0);
x_374 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_373);
x_375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_array_get_size(x_4);
x_377 = lean_usize_of_nat(x_376);
lean_dec(x_376);
x_378 = 0;
x_379 = x_4;
x_380 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_381 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_382 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_380, x_381, x_377, x_378, x_379);
x_383 = x_382;
x_384 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
x_385 = l_Lean_mkSepArray(x_383, x_384);
lean_dec(x_383);
x_386 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_387 = l_Array_append___rarg(x_386, x_385);
x_388 = lean_box(2);
x_389 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_390 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
lean_ctor_set(x_390, 2, x_387);
x_391 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
x_392 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_392, 0, x_373);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_394 = lean_array_push(x_393, x_375);
x_395 = lean_array_push(x_394, x_381);
x_396 = lean_array_push(x_395, x_390);
x_397 = lean_array_push(x_396, x_381);
x_398 = lean_array_push(x_397, x_392);
x_399 = lean_array_push(x_398, x_1);
x_400 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17;
x_401 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_401, 0, x_388);
lean_ctor_set(x_401, 1, x_400);
lean_ctor_set(x_401, 2, x_399);
lean_ctor_set(x_371, 0, x_401);
return x_371;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; size_t x_407; size_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_402 = lean_ctor_get(x_371, 0);
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_371);
x_404 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_402);
x_405 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_array_get_size(x_4);
x_407 = lean_usize_of_nat(x_406);
lean_dec(x_406);
x_408 = 0;
x_409 = x_4;
x_410 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_411 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_412 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_410, x_411, x_407, x_408, x_409);
x_413 = x_412;
x_414 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
x_415 = l_Lean_mkSepArray(x_413, x_414);
lean_dec(x_413);
x_416 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_417 = l_Array_append___rarg(x_416, x_415);
x_418 = lean_box(2);
x_419 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_420 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
lean_ctor_set(x_420, 2, x_417);
x_421 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
x_422 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_422, 0, x_402);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_424 = lean_array_push(x_423, x_405);
x_425 = lean_array_push(x_424, x_411);
x_426 = lean_array_push(x_425, x_420);
x_427 = lean_array_push(x_426, x_411);
x_428 = lean_array_push(x_427, x_422);
x_429 = lean_array_push(x_428, x_1);
x_430 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17;
x_431 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_431, 0, x_418);
lean_ctor_set(x_431, 1, x_430);
lean_ctor_set(x_431, 2, x_429);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_403);
return x_432;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__1(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___spec__2(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
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
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_3, x_6, x_20, x_19, x_5);
lean_dec(x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
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
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_20, x_5, x_21, x_19, x_4);
lean_dec(x_5);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = l_Lean_Elab_Term_expandFunBinders_loop___closed__4;
lean_inc(x_1);
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
lean_inc(x_2);
x_15 = lean_array_push(x_14, x_2);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = x_18;
x_22 = lean_array_uset(x_10, x_4, x_21);
x_4 = x_20;
x_5 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_15);
lean_ctor_set(x_5, 2, x_12);
lean_inc(x_5);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_23 = l_Lean_addMacroScope(x_15, x_22, x_12);
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_23);
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_28 = lean_array_push(x_27, x_21);
x_29 = lean_array_push(x_28, x_26);
x_30 = lean_box(2);
x_31 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_array_push(x_4, x_32);
lean_inc(x_5);
x_34 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_33, x_5, x_19);
lean_dec(x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_20);
x_41 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_39);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_39);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_23);
lean_ctor_set(x_43, 3, x_24);
x_44 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_45 = lean_array_push(x_44, x_43);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
x_48 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_51 = lean_array_push(x_50, x_47);
x_52 = lean_array_push(x_51, x_49);
x_53 = lean_array_push(x_52, x_35);
x_54 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_30);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
x_56 = lean_array_push(x_27, x_42);
x_57 = lean_array_push(x_56, x_55);
x_58 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_30);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
x_60 = lean_array_push(x_27, x_40);
x_61 = lean_array_push(x_60, x_59);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_30);
lean_ctor_set(x_62, 1, x_31);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_37, 0, x_62);
return x_37;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_63 = lean_ctor_get(x_37, 0);
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_37);
lean_inc(x_63);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_20);
x_66 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_63);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_63);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_25);
lean_ctor_set(x_68, 2, x_23);
lean_ctor_set(x_68, 3, x_24);
x_69 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_70 = lean_array_push(x_69, x_68);
x_71 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_30);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_70);
x_73 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_76 = lean_array_push(x_75, x_72);
x_77 = lean_array_push(x_76, x_74);
x_78 = lean_array_push(x_77, x_35);
x_79 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_30);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_78);
x_81 = lean_array_push(x_27, x_67);
x_82 = lean_array_push(x_81, x_80);
x_83 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_30);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_array_push(x_27, x_65);
x_86 = lean_array_push(x_85, x_84);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_30);
lean_ctor_set(x_87, 1, x_31);
lean_ctor_set(x_87, 2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_64);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_23);
lean_dec(x_5);
x_89 = !lean_is_exclusive(x_34);
if (x_89 == 0)
{
return x_34;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_34, 0);
x_91 = lean_ctor_get(x_34, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_34);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
x_97 = lean_ctor_get(x_5, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_94);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_12);
lean_ctor_set(x_98, 3, x_95);
lean_ctor_set(x_98, 4, x_96);
lean_ctor_set(x_98, 5, x_97);
lean_inc(x_98);
x_99 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_98, x_6);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
lean_inc(x_100);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_105 = l_Lean_addMacroScope(x_94, x_104, x_12);
x_106 = lean_box(0);
x_107 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_105);
x_108 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_108, 0, x_100);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_106);
x_109 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_110 = lean_array_push(x_109, x_103);
x_111 = lean_array_push(x_110, x_108);
x_112 = lean_box(2);
x_113 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_111);
x_115 = lean_array_push(x_4, x_114);
lean_inc(x_98);
x_116 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_115, x_98, x_101);
lean_dec(x_10);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_98, x_118);
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
lean_inc(x_120);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_102);
x_124 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_120);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_120);
x_126 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_107);
lean_ctor_set(x_126, 2, x_105);
lean_ctor_set(x_126, 3, x_106);
x_127 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_128 = lean_array_push(x_127, x_126);
x_129 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_112);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_128);
x_131 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_120);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_134 = lean_array_push(x_133, x_130);
x_135 = lean_array_push(x_134, x_132);
x_136 = lean_array_push(x_135, x_117);
x_137 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_112);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_136);
x_139 = lean_array_push(x_109, x_125);
x_140 = lean_array_push(x_139, x_138);
x_141 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_112);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_140);
x_143 = lean_array_push(x_109, x_123);
x_144 = lean_array_push(x_143, x_142);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_112);
lean_ctor_set(x_145, 1, x_113);
lean_ctor_set(x_145, 2, x_144);
if (lean_is_scalar(x_122)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_122;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_121);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_105);
lean_dec(x_98);
x_147 = lean_ctor_get(x_116, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_116, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_149 = x_116;
} else {
 lean_dec_ref(x_116);
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
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_151 = lean_ctor_get(x_6, 0);
x_152 = lean_ctor_get(x_6, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_6);
x_153 = lean_nat_add(x_151, x_9);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_ctor_get(x_5, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_5, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_5, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_5, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_5, 5);
lean_inc(x_159);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_160 = x_5;
} else {
 lean_dec_ref(x_5);
 x_160 = lean_box(0);
}
lean_inc(x_151);
lean_inc(x_156);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 6, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_151);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set(x_161, 4, x_158);
lean_ctor_set(x_161, 5, x_159);
lean_inc(x_161);
x_162 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_161, x_154);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
lean_inc(x_163);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_168 = l_Lean_addMacroScope(x_156, x_167, x_151);
x_169 = lean_box(0);
x_170 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_168);
x_171 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_171, 0, x_163);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
x_172 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_173 = lean_array_push(x_172, x_166);
x_174 = lean_array_push(x_173, x_171);
x_175 = lean_box(2);
x_176 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_174);
x_178 = lean_array_push(x_4, x_177);
lean_inc(x_161);
x_179 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_10, x_178, x_161, x_164);
lean_dec(x_10);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_161, x_181);
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
lean_inc(x_183);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_165);
x_187 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_183);
x_188 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
lean_inc(x_183);
x_189 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_170);
lean_ctor_set(x_189, 2, x_168);
lean_ctor_set(x_189, 3, x_169);
x_190 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_191 = lean_array_push(x_190, x_189);
x_192 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_175);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_191);
x_194 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_183);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_197 = lean_array_push(x_196, x_193);
x_198 = lean_array_push(x_197, x_195);
x_199 = lean_array_push(x_198, x_180);
x_200 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_175);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_199);
x_202 = lean_array_push(x_172, x_188);
x_203 = lean_array_push(x_202, x_201);
x_204 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_175);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_203);
x_206 = lean_array_push(x_172, x_186);
x_207 = lean_array_push(x_206, x_205);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_175);
lean_ctor_set(x_208, 1, x_176);
lean_ctor_set(x_208, 2, x_207);
if (lean_is_scalar(x_185)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_185;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_184);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_168);
lean_dec(x_161);
x_210 = lean_ctor_get(x_179, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_179, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_212 = x_179;
} else {
 lean_dec_ref(x_179);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
lean_object* x_214; uint8_t x_215; 
lean_inc(x_5);
x_214 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_5, x_6);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; size_t x_221; size_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
x_218 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_216);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_array_get_size(x_4);
x_221 = lean_usize_of_nat(x_220);
lean_dec(x_220);
x_222 = 0;
x_223 = x_4;
x_224 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_225 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_226 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_224, x_225, x_221, x_222, x_223);
x_227 = x_226;
x_228 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
x_229 = l_Lean_mkSepArray(x_227, x_228);
lean_dec(x_227);
x_230 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_231 = l_Array_append___rarg(x_230, x_229);
x_232 = lean_box(2);
x_233 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_234 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_231);
x_235 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_216);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_238 = lean_array_push(x_237, x_219);
x_239 = lean_array_push(x_238, x_225);
x_240 = lean_array_push(x_239, x_234);
x_241 = lean_array_push(x_240, x_225);
x_242 = lean_array_push(x_241, x_236);
x_243 = lean_array_push(x_242, x_1);
x_244 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_245 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_245, 0, x_232);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set(x_245, 2, x_243);
x_246 = l_Lean_Syntax_isNone(x_2);
if (x_246 == 0)
{
lean_object* x_247; 
lean_free_object(x_214);
x_247 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_245, x_5, x_217);
return x_247;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_214, 0, x_245);
return x_214;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; size_t x_253; size_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_248 = lean_ctor_get(x_214, 0);
x_249 = lean_ctor_get(x_214, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_214);
x_250 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_248);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_array_get_size(x_4);
x_253 = lean_usize_of_nat(x_252);
lean_dec(x_252);
x_254 = 0;
x_255 = x_4;
x_256 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_257 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_258 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_256, x_257, x_253, x_254, x_255);
x_259 = x_258;
x_260 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16;
x_261 = l_Lean_mkSepArray(x_259, x_260);
lean_dec(x_259);
x_262 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_263 = l_Array_append___rarg(x_262, x_261);
x_264 = lean_box(2);
x_265 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_266 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set(x_266, 2, x_263);
x_267 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_248);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_270 = lean_array_push(x_269, x_251);
x_271 = lean_array_push(x_270, x_257);
x_272 = lean_array_push(x_271, x_266);
x_273 = lean_array_push(x_272, x_257);
x_274 = lean_array_push(x_273, x_268);
x_275 = lean_array_push(x_274, x_1);
x_276 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_264);
lean_ctor_set(x_277, 1, x_276);
lean_ctor_set(x_277, 2, x_275);
x_278 = l_Lean_Syntax_isNone(x_2);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_2, x_277, x_5, x_249);
return x_279;
}
else
{
lean_object* x_280; 
lean_dec(x_5);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_249);
return x_280;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___spec__1(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getMatchAltsNumPatterns(x_5);
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_10 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_5, x_7, x_8, x_9, x_2, x_3);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAltsWhereDecls(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
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
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
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
x_37 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_34);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_39);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_43 = l_Array_append___rarg(x_42, x_35);
x_44 = lean_box(2);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_43);
x_47 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_50 = lean_array_push(x_49, x_46);
x_51 = lean_array_push(x_50, x_48);
x_52 = lean_array_push(x_51, x_36);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_10);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_55 = lean_array_push(x_54, x_41);
x_56 = lean_array_push(x_55, x_53);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_4);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_37, 0, x_57);
return x_37;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_58 = lean_ctor_get(x_37, 0);
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_37);
x_60 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_58);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
x_63 = l_Array_append___rarg(x_62, x_35);
x_64 = lean_box(2);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_63);
x_67 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Elab_Term_quoteAutoTactic___closed__34;
x_70 = lean_array_push(x_69, x_66);
x_71 = lean_array_push(x_70, x_68);
x_72 = lean_array_push(x_71, x_36);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_10);
lean_ctor_set(x_73, 2, x_72);
x_74 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_75 = lean_array_push(x_74, x_61);
x_76 = lean_array_push(x_75, x_73);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_4);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_59);
return x_78;
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
x_1 = lean_mk_string("expandFun");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_expandFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFun), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_expandFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Term_expandFun___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_expandFun___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_1);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_9);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_6, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_18, 0, x_13);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_15);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_15);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = x_21;
x_23 = lean_ctor_get(x_7, 3);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_st_ref_get(x_8, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_environment_main_module(x_13);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_23);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_apply_2(x_1, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_st_ref_take(x_8, x_31);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_42, 1);
lean_dec(x_45);
lean_ctor_set(x_42, 1, x_40);
x_46 = lean_st_ref_set(x_8, x_42, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_List_reverse___rarg(x_48);
x_50 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_38);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 2);
x_57 = lean_ctor_get(x_42, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_40);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_st_ref_set(x_8, x_58, x_43);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
lean_dec(x_39);
x_62 = l_List_reverse___rarg(x_61);
x_63 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_66, 0, x_38);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
lean_dec(x_37);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_throwErrorAt___at_Lean_Elab_Term_precheckFun___spec__2(x_68, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_72;
}
else
{
lean_object* x_73; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4___rarg(x_31);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
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
x_24 = lean_usize_add(x_3, x_23);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
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
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__5(x_17, x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
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
x_26 = lean_usize_add(x_3, x_25);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
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
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_14, x_20);
lean_dec(x_14);
x_22 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_array_get_size(x_28);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__6(x_28, x_31, x_32, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_37, 0, x_29);
x_38 = l_Lean_Elab_Term_Quotation_withNewLocals___rarg(x_35, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_35);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_precheckFun___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_precheckFun___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_precheckFun___spec__6(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precheckFun");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_precheckFun), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_precheckFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Term_precheckFun___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_precheckFun___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_1);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_8);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_15, 0, x_12);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_17, 0, x_12);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_19, 0, x_12);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = x_20;
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_7, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_12);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_22);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_2(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_st_ref_take(x_7, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_39);
x_45 = lean_st_ref_set(x_7, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_List_reverse___rarg(x_47);
x_49 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_37);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 2);
x_56 = lean_ctor_get(x_41, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_42);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
lean_dec(x_36);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_throwErrorAt___at_Lean_Elab_Term_elabFun___spec__2(x_67, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4___rarg(x_30);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
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
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
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
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_14, x_20);
lean_dec(x_14);
x_22 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabFun___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun___lambda__1), 10, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_Term_elabFunBinders___rarg(x_28, x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_28);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabFun___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_1 = lean_mk_string("elabFun");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Term_elabFun___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabFun___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1), 10, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___lambda__1), 9, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected error when elaborating 'let'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_26 = l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__3), 11, 2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
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
x_22 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
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
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_addLocalVarInfo(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_3, x_16, x_16, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_instantiateMVars(x_18, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_24 = lean_array_push(x_23, x_5);
x_25 = 0;
x_26 = l_Lean_Meta_mkLambdaFVars(x_24, x_21, x_25, x_4, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
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
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_dec(x_11);
if (x_6 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = l_Lean_Syntax_getId(x_7);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__5), 11, 3);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_8);
lean_closure_set(x_20, 2, x_9);
x_21 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_22 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_19, x_21, x_5, x_20, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_4);
x_25 = l_Lean_mkApp(x_23, x_4);
x_26 = l_Lean_mkLetFunAnnotation(x_25);
x_27 = l_Lean_Elab_Term_elabLetDeclAux___lambda__4(x_1, x_2, x_3, x_4, x_5, x_26, x_12, x_13, x_14, x_15, x_16, x_17, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Syntax_getId(x_7);
x_33 = lean_box(x_10);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__6___boxed), 12, 4);
lean_closure_set(x_34, 0, x_7);
lean_closure_set(x_34, 1, x_8);
lean_closure_set(x_34, 2, x_9);
lean_closure_set(x_34, 3, x_33);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_5);
x_35 = l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_32, x_5, x_4, x_34, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_elabLetDeclAux___lambda__4(x_1, x_2, x_3, x_4, x_5, x_36, x_12, x_13, x_14, x_15, x_16, x_17, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
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
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_8);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed), 11, 3);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_19 = l_Lean_Elab_Term_elabBinders___rarg(x_2, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
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
x_26 = l_Lean_Elab_Term_elabLetDeclAux___closed__3;
x_49 = lean_st_ref_get(x_15, x_22);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = 0;
x_27 = x_54;
x_28 = x_53;
goto block_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_26, x_10, x_11, x_12, x_13, x_14, x_15, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unbox(x_57);
lean_dec(x_57);
x_27 = x_59;
x_28 = x_58;
goto block_48;
}
block_48:
{
if (x_27 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Term_elabLetDeclAux___lambda__7(x_8, x_25, x_4, x_24, x_23, x_7, x_1, x_5, x_6, x_9, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = l_Lean_Syntax_getId(x_1);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_Term_elabLetDeclAux___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_Term_elabLetDeclAux___closed__6;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_23);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_23);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Term_elabLetDeclAux___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_24);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_24);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_26, x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Term_elabLetDeclAux___lambda__7(x_8, x_25, x_4, x_24, x_23, x_7, x_1, x_5, x_6, x_9, x_45, x_10, x_11, x_12, x_13, x_14, x_15, x_46);
return x_47;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_elabLetDeclAux___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabLetDeclAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lambda__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Elab_Term_elabLetDeclAux___lambda__6(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lambda__7___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_1);
lean_dec(x_1);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_10);
lean_dec(x_10);
x_22 = l_Lean_Elab_Term_elabLetDeclAux___lambda__7(x_19, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Lean_Elab_Term_elabLetDeclAux(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object* x_1) {
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
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_expandOptType(x_3, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkLetIdDeclView(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letIdDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Term_elabLetDeclAux___closed__7;
x_17 = l_Lean_mkAtomFrom(x_1, x_16);
x_18 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__3;
x_19 = lean_array_push(x_18, x_11);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_17);
x_23 = lean_array_push(x_22, x_9);
x_24 = lean_box(2);
x_25 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = l_Lean_Elab_Term_elabLetDeclAux___closed__7;
x_36 = l_Lean_mkAtomFrom(x_1, x_35);
x_37 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__3;
x_38 = lean_array_push(x_37, x_30);
x_39 = lean_array_push(x_38, x_32);
x_40 = lean_array_push(x_39, x_34);
x_41 = lean_array_push(x_40, x_36);
x_42 = lean_array_push(x_41, x_27);
x_43 = lean_box(2);
x_44 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_28);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabLetDeclCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_15, 0, x_12);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_17, 0, x_12);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_precheckFun___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_19, 0, x_12);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = x_20;
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_7, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_12);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_22);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_2(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_st_ref_take(x_7, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_39);
x_45 = lean_st_ref_set(x_7, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_List_reverse___rarg(x_47);
x_49 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_37);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 2);
x_56 = lean_ctor_get(x_41, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_42);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
lean_dec(x_36);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_throwErrorAt___at_Lean_Elab_Term_quoteAutoTactic___spec__4(x_67, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_30);
return x_72;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letPatDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letEqnsDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeSpec");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let_fun");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Binders");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.elabLetDeclCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_elabLetDeclCore___closed__14;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__15;
x_3 = lean_unsigned_to_nat(616u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Elab_Term_elabLetDeclCore___closed__16;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let_delayed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l_Lean_Elab_Term_elabLetDeclCore___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_inc(x_16);
x_19 = l_Lean_Syntax_getKind(x_16);
x_20 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_23 = lean_name_eq(x_19, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
x_24 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
x_25 = lean_name_eq(x_19, x_24);
lean_dec(x_19);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl), 3, 1);
lean_closure_set(x_27, 0, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_elabLetDeclCore___spec__1(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Syntax_setArg(x_14, x_15, x_29);
lean_inc(x_1);
x_32 = l_Lean_Syntax_setArg(x_1, x_13, x_31);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_box(x_33);
lean_inc(x_32);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_36, 0, x_32);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_34);
lean_closure_set(x_36, 3, x_35);
x_37 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_32, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_19);
lean_dec(x_14);
x_42 = l_Lean_Syntax_getArg(x_16, x_15);
x_43 = lean_unsigned_to_nat(2u);
x_44 = l_Lean_Syntax_getArg(x_16, x_43);
lean_inc(x_42);
x_45 = l_Lean_Elab_Term_expandOptType(x_42, x_44);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(4u);
x_47 = l_Lean_Syntax_getArg(x_16, x_46);
lean_dec(x_16);
lean_inc(x_10);
x_48 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__2___rarg(x_10, x_11, x_12);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_getMainModule___rarg(x_11, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
lean_inc(x_49);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2;
x_60 = l_Lean_addMacroScope(x_55, x_59, x_52);
x_61 = lean_box(0);
x_62 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_49);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_61);
x_64 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
lean_inc(x_49);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9;
x_67 = lean_array_push(x_66, x_65);
x_68 = lean_array_push(x_67, x_45);
x_69 = lean_box(2);
x_70 = l_Lean_Elab_Term_elabLetDeclCore___closed__9;
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_68);
x_72 = l_Lean_Elab_Term_quoteAutoTactic___closed__39;
x_73 = lean_array_push(x_72, x_71);
x_74 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8;
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_73);
x_76 = l_Lean_Elab_Term_elabLetDeclCore___closed__11;
lean_inc(x_49);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_49);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__3;
lean_inc(x_63);
x_79 = lean_array_push(x_78, x_63);
x_80 = l_Lean_Elab_Term_expandFunBinders_loop___closed__3;
x_81 = lean_array_push(x_79, x_80);
x_82 = lean_array_push(x_81, x_75);
x_83 = lean_array_push(x_82, x_77);
x_84 = lean_array_push(x_83, x_47);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_69);
lean_ctor_set(x_85, 1, x_20);
lean_ctor_set(x_85, 2, x_84);
x_86 = lean_array_push(x_72, x_85);
x_87 = l_Lean_Elab_Term_elabLetDeclCore___closed__7;
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_69);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_86);
x_89 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
lean_inc(x_49);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_49);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_push(x_72, x_90);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_69);
lean_ctor_set(x_92, 1, x_74);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
lean_inc(x_49);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_49);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_Term_expandFunBinders_loop___closed__6;
x_96 = lean_array_push(x_95, x_63);
x_97 = l_Lean_Elab_Term_expandFunBinders_loop___closed__5;
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_69);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_96);
x_99 = lean_array_push(x_72, x_98);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_69);
lean_ctor_set(x_100, 1, x_74);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_Lean_Elab_Term_expandFunBinders_loop___closed__7;
lean_inc(x_49);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_49);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Term_expandFunBinders_loop___closed__12;
lean_inc(x_49);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_49);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_push(x_72, x_42);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_69);
lean_ctor_set(x_106, 1, x_74);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lean_Elab_Term_expandFunBinders_loop___closed__13;
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_49);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Elab_Term_expandFunBinders_loop___closed__14;
x_110 = lean_array_push(x_109, x_104);
x_111 = lean_array_push(x_110, x_106);
x_112 = lean_array_push(x_111, x_108);
x_113 = lean_array_push(x_112, x_18);
x_114 = l_Lean_Elab_Term_expandFunBinders_loop___closed__11;
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_69);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_113);
x_116 = lean_array_push(x_72, x_115);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_69);
lean_ctor_set(x_117, 1, x_74);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_array_push(x_72, x_117);
x_119 = l_Lean_Elab_Term_expandFunBinders_loop___closed__9;
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_69);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_118);
x_121 = l_Lean_Elab_Term_expandFunBinders_loop___closed__15;
x_122 = lean_array_push(x_121, x_94);
x_123 = lean_array_push(x_122, x_80);
x_124 = lean_array_push(x_123, x_100);
x_125 = lean_array_push(x_124, x_80);
x_126 = lean_array_push(x_125, x_102);
x_127 = lean_array_push(x_126, x_120);
x_128 = l_Lean_Elab_Term_expandFunBinders_loop___closed__2;
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_69);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
x_130 = lean_array_push(x_109, x_58);
x_131 = lean_array_push(x_130, x_88);
x_132 = lean_array_push(x_131, x_92);
x_133 = lean_array_push(x_132, x_129);
x_134 = l_Lean_Elab_Term_elabLetDeclCore___closed__5;
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_69);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_133);
if (x_3 == 0)
{
if (x_4 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_136 = l_Lean_Elab_Term_elabLetDeclCore___closed__13;
x_137 = l_Lean_Syntax_setKind(x_135, x_136);
x_138 = 1;
x_139 = lean_box(x_138);
x_140 = lean_box(x_138);
lean_inc(x_137);
x_141 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_141, 0, x_137);
lean_closure_set(x_141, 1, x_2);
lean_closure_set(x_141, 2, x_139);
lean_closure_set(x_141, 3, x_140);
x_142 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_137, x_141, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_135);
x_143 = l_Lean_Elab_Term_elabLetDeclCore___closed__17;
x_144 = l_panic___at_Lean_Elab_Term_resolveName_x27___spec__3(x_143);
x_145 = 1;
x_146 = lean_box(x_145);
x_147 = lean_box(x_145);
lean_inc(x_144);
x_148 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_148, 0, x_144);
lean_closure_set(x_148, 1, x_2);
lean_closure_set(x_148, 2, x_146);
lean_closure_set(x_148, 3, x_147);
x_149 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_144, x_148, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
return x_149;
}
}
else
{
if (x_4 == 0)
{
uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = 1;
x_151 = lean_box(x_150);
x_152 = lean_box(x_150);
lean_inc(x_135);
x_153 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_153, 0, x_135);
lean_closure_set(x_153, 1, x_2);
lean_closure_set(x_153, 2, x_151);
lean_closure_set(x_153, 3, x_152);
x_154 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_135, x_153, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = l_Lean_Elab_Term_elabLetDeclCore___closed__19;
x_156 = l_Lean_Syntax_setKind(x_135, x_155);
x_157 = 1;
x_158 = lean_box(x_157);
x_159 = lean_box(x_157);
lean_inc(x_156);
x_160 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_160, 0, x_156);
lean_closure_set(x_160, 1, x_2);
lean_closure_set(x_160, 2, x_158);
lean_closure_set(x_160, 3, x_159);
x_161 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_156, x_160, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
return x_161;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_1);
x_162 = l_Lean_Elab_Term_mkLetIdDeclView(x_16);
lean_dec(x_16);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 3);
lean_inc(x_166);
lean_dec(x_162);
x_167 = l_Lean_Elab_Term_elabLetDeclAux(x_163, x_164, x_165, x_166, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_167;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_11, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabLetDecl");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDecl), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabLetDeclCore___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabLetFunDecl");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetFunDecl), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabLetDeclCore___closed__13;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabLetDelayedDecl");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDelayedDecl), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Elab_Term_elabLetDeclCore___closed__19;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_11, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let_tmp");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabLetTmpDecl");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabForall___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetTmpDecl), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_6817_(lean_object* x_1) {
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
lean_object* initialize_Lean_Elab_BindersUtil(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Binders(lean_object* w) {
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
res = initialize_Lean_Elab_BindersUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1 = _init_l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__1);
l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2 = _init_l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___spec__2___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_quoteAutoTactic___spec__3___closed__11);
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
l_Lean_Elab_Term_quoteAutoTactic___closed__30 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__30();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__30);
l_Lean_Elab_Term_quoteAutoTactic___closed__31 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__31();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__31);
l_Lean_Elab_Term_quoteAutoTactic___closed__32 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__32();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__32);
l_Lean_Elab_Term_quoteAutoTactic___closed__33 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__33();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__33);
l_Lean_Elab_Term_quoteAutoTactic___closed__34 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__34();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__34);
l_Lean_Elab_Term_quoteAutoTactic___closed__35 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__35();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__35);
l_Lean_Elab_Term_quoteAutoTactic___closed__36 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__36();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__36);
l_Lean_Elab_Term_quoteAutoTactic___closed__37 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__37();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__37);
l_Lean_Elab_Term_quoteAutoTactic___closed__38 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__38();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__38);
l_Lean_Elab_Term_quoteAutoTactic___closed__39 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__39();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__39);
l_Lean_Elab_Term_quoteAutoTactic___closed__40 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__40();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__40);
l_Lean_Elab_Term_quoteAutoTactic___closed__41 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__41();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__41);
l_Lean_Elab_Term_quoteAutoTactic___closed__42 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__42();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__42);
l_Lean_Elab_Term_quoteAutoTactic___closed__43 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__43();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__43);
l_Lean_Elab_Term_quoteAutoTactic___closed__44 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__44();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__44);
l_Lean_Elab_Term_quoteAutoTactic___closed__45 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__45();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__45);
l_Lean_Elab_Term_quoteAutoTactic___closed__46 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__46();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__46);
l_Lean_Elab_Term_quoteAutoTactic___closed__47 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__47();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__47);
l_Lean_Elab_Term_quoteAutoTactic___closed__48 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__48();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__48);
l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1 = _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__1);
l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__2 = _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__2);
l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3 = _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__3);
l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4 = _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__4);
l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5 = _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__5);
l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__6 = _init_l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___lambda__2___closed__6);
l_Lean_Elab_Term_declareTacticSyntax___closed__1 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__1);
l_Lean_Elab_Term_declareTacticSyntax___closed__2 = _init_l_Lean_Elab_Term_declareTacticSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg___closed__1);
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
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__9);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__10);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__11 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__11);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__12);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__13);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__14 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__14);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___closed__15);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___spec__1___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed__const__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__9);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__10 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_matchBinder___closed__10);
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
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__3);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__4 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__4);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__5 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431____closed__5);
l_Lean_Elab_Term_checkBinderAnnotations___closed__1 = _init_l_Lean_Elab_Term_checkBinderAnnotations___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_checkBinderAnnotations___closed__1);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_1431_(lean_io_mk_world());
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
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___rarg___closed__1);
l_Lean_Elab_Term_elabForall___closed__1 = _init_l_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___closed__1);
l_Lean_Elab_Term_elabForall___closed__2 = _init_l_Lean_Elab_Term_elabForall___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___closed__2);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__1);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__2);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__3);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__4);
l___regBuiltin_Lean_Elab_Term_elabForall___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabForall___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabForall___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabArrow___closed__1 = _init_l_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__1);
l_Lean_Elab_Term_elabArrow___closed__2 = _init_l_Lean_Elab_Term_elabArrow___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__2);
l_Lean_Elab_Term_elabArrow___closed__3 = _init_l_Lean_Elab_Term_elabArrow___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__3);
l_Lean_Elab_Term_elabArrow___closed__4 = _init_l_Lean_Elab_Term_elabArrow___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__4);
l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabArrow___closed__1);
l___regBuiltin_Lean_Elab_Term_elabArrow___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabArrow___closed__2);
l___regBuiltin_Lean_Elab_Term_elabArrow___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabArrow___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabArrow___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__2);
l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__3);
l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__4);
l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDepArrow___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabDepArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___spec__3___closed__2);
l_Lean_Elab_Term_expandFunBinders_loop___closed__1 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__1);
l_Lean_Elab_Term_expandFunBinders_loop___closed__2 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__2);
l_Lean_Elab_Term_expandFunBinders_loop___closed__3 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__3);
l_Lean_Elab_Term_expandFunBinders_loop___closed__4 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__4);
l_Lean_Elab_Term_expandFunBinders_loop___closed__5 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__5);
l_Lean_Elab_Term_expandFunBinders_loop___closed__6 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__6);
l_Lean_Elab_Term_expandFunBinders_loop___closed__7 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__7);
l_Lean_Elab_Term_expandFunBinders_loop___closed__8 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__8);
l_Lean_Elab_Term_expandFunBinders_loop___closed__9 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__9);
l_Lean_Elab_Term_expandFunBinders_loop___closed__10 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__10);
l_Lean_Elab_Term_expandFunBinders_loop___closed__11 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__11);
l_Lean_Elab_Term_expandFunBinders_loop___closed__12 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__12);
l_Lean_Elab_Term_expandFunBinders_loop___closed__13 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__13);
l_Lean_Elab_Term_expandFunBinders_loop___closed__14 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__14);
l_Lean_Elab_Term_expandFunBinders_loop___closed__15 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__15);
l_Lean_Elab_Term_expandFunBinders_loop___closed__16 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__16);
l_Lean_Elab_Term_expandFunBinders_loop___closed__17 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__17);
l_Lean_Elab_Term_expandFunBinders_loop___closed__18 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__18);
l_Lean_Elab_Term_FunBinders_State_fvars___default = _init_l_Lean_Elab_Term_FunBinders_State_fvars___default();
lean_mark_persistent(l_Lean_Elab_Term_FunBinders_State_fvars___default);
l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default = _init_l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default();
lean_mark_persistent(l_Lean_Elab_Term_FunBinders_State_expectedType_x3f___default);
l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__1 = _init_l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__1);
l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2 = _init_l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__2);
l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__3 = _init_l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___lambda__2___closed__3);
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
l_Lean_Elab_Term_expandWhereDecls___closed__6 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__6);
l_Lean_Elab_Term_expandWhereDecls___closed__7 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__7);
l_Lean_Elab_Term_expandWhereDecls___closed__8 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__8);
l_Lean_Elab_Term_expandWhereDecls___closed__9 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__9);
l_Lean_Elab_Term_expandWhereDecls___closed__10 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__10);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__15);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__16);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__17);
l___regBuiltin_Lean_Elab_Term_expandFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandFun___closed__1);
l___regBuiltin_Lean_Elab_Term_expandFun___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandFun___closed__2);
l___regBuiltin_Lean_Elab_Term_expandFun___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_expandFun___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandFun___closed__3);
res = l___regBuiltin_Lean_Elab_Term_expandFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_precheckFun___closed__1);
l___regBuiltin_Lean_Elab_Term_precheckFun___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_precheckFun___closed__2);
l___regBuiltin_Lean_Elab_Term_precheckFun___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_precheckFun___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_precheckFun___closed__3);
res = l___regBuiltin_Lean_Elab_Term_precheckFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabFun___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabFun___closed__1);
l___regBuiltin_Lean_Elab_Term_elabFun___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabFun___closed__2);
l___regBuiltin_Lean_Elab_Term_elabFun___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabFun___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabFun___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__1___closed__3);
l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lambda__3___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__3);
l_Lean_Elab_Term_elabLetDeclAux___closed__4 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__4);
l_Lean_Elab_Term_elabLetDeclAux___closed__5 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__5);
l_Lean_Elab_Term_elabLetDeclAux___closed__6 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__6);
l_Lean_Elab_Term_elabLetDeclAux___closed__7 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__7);
l_Lean_Elab_Term_elabLetDeclAux___closed__8 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__8);
l_Lean_Elab_Term_expandLetEqnsDecl___closed__1 = _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandLetEqnsDecl___closed__1);
l_Lean_Elab_Term_expandLetEqnsDecl___closed__2 = _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandLetEqnsDecl___closed__2);
l_Lean_Elab_Term_expandLetEqnsDecl___closed__3 = _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandLetEqnsDecl___closed__3);
l_Lean_Elab_Term_elabLetDeclCore___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__1);
l_Lean_Elab_Term_elabLetDeclCore___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__2);
l_Lean_Elab_Term_elabLetDeclCore___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__3);
l_Lean_Elab_Term_elabLetDeclCore___closed__4 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__4);
l_Lean_Elab_Term_elabLetDeclCore___closed__5 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__5);
l_Lean_Elab_Term_elabLetDeclCore___closed__6 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__6);
l_Lean_Elab_Term_elabLetDeclCore___closed__7 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__7);
l_Lean_Elab_Term_elabLetDeclCore___closed__8 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__8);
l_Lean_Elab_Term_elabLetDeclCore___closed__9 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__9);
l_Lean_Elab_Term_elabLetDeclCore___closed__10 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__10);
l_Lean_Elab_Term_elabLetDeclCore___closed__11 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__11);
l_Lean_Elab_Term_elabLetDeclCore___closed__12 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__12);
l_Lean_Elab_Term_elabLetDeclCore___closed__13 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__13);
l_Lean_Elab_Term_elabLetDeclCore___closed__14 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__14);
l_Lean_Elab_Term_elabLetDeclCore___closed__15 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__15);
l_Lean_Elab_Term_elabLetDeclCore___closed__16 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__16);
l_Lean_Elab_Term_elabLetDeclCore___closed__17 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__17);
l_Lean_Elab_Term_elabLetDeclCore___closed__18 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__18);
l_Lean_Elab_Term_elabLetDeclCore___closed__19 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__19);
l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDecl___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabLetDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetFunDecl___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabLetFunDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__3);
l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__4);
l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl___closed__5);
res = l___regBuiltin_Lean_Elab_Term_elabLetTmpDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_6817_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
