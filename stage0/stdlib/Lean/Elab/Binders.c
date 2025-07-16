// Lean compiler output
// Module: Lean.Elab.Binders
// Imports: Lean.Elab.Quotation.Precheck Lean.Elab.Term Lean.Elab.BindersUtil Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.TerminationHint Lean.Elab.Match Lean.Compiler.MetaAttr
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
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7;
static lean_object* l_Lean_Elab_Term_mkLetIdDeclView___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___closed__0;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed(lean_object**);
static lean_object* l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMeta(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_14753_;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__0;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_14753_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1;
static lean_object* l_Lean_Elab_Term_elabHaveIDecl___closed__0;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__5;
static lean_object* l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_14753_;
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__4;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__6;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__0;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__20;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14;
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkLetConfig___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1;
static lean_object* l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_Binders___hyg_14753_;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__3;
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__8;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__8;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__10;
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__0;
static lean_object* l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__1;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__12;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__7;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__24;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__12;
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__3;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__3;
static lean_object* l_Lean_Elab_Term_elabHaveDecl___closed__0;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__14;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__8;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_14753_;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__4;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__7;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_object* l_Lean_MessageData_note(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__20;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1;
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__6;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__11;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__7;
static lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__1;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__7;
extern lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
static lean_object* l_Lean_Elab_Term_expandForall___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__4;
lean_object* l_Array_unzip___redArg(lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__6;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__12;
static lean_object* l_Lean_Elab_Term_elabFunBinders___redArg___closed__0;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetIDecl___closed__0;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1(lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__10;
static lean_object* l_Lean_Elab_Term_mkLetConfig___closed__1;
static lean_object* l_Lean_Elab_Term_precheckFun___closed__0;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__27;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__0;
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__4;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2;
static lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___closed__0;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__3;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__4;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__3;
lean_object* l_Lean_Elab_Term_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1(lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9;
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3;
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___closed__1;
static lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__1;
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__3;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__4;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_LetConfig_setFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__0;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__4;
static lean_object* l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__1;
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
static lean_object* l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_Binders___hyg_14753_;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_Binders___hyg_14753_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__6;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__4;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__22;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_Binders___hyg_14753_;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__12;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_14753_(lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3;
static lean_object* l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_Binders___hyg_14753_;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__9;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__3;
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__2;
static lean_object* l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__3;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__3;
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__2;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkBinderAnnotations;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__16;
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkLetIdDeclView___closed__0;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__17;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__28;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__13;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDeclsOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__1;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__1;
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_Binders___hyg_14753_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_precheckArrow___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__0;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__9;
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__16;
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__0;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__6;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__10;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__1;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9;
lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_____private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_LetConfig_setFrom___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__1;
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_kindOfBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
static lean_object* l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__0;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetIDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_quoteAutoTactic___lam__0(lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_2354_;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__1;
static lean_object* l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_Binders___hyg_14753_;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__5;
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__5;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__3;
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__0;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___closed__1;
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__6;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__5;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__5;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMapM___at___Lean_Elab_Term_getMatchAlts_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_14753_;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabBinder___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3___closed__0;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__25;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__11;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__7;
lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1;
lean_object* l_Lean_Linter_getLinterOptions___at___Lean_Linter_checkDeprecated___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_checkDeprecatedCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Term_elabArrow___redArg___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__4;
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__5;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__18;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__3;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9;
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__13;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_kindOfBinderName___boxed(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_Binders___hyg_14753_;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__5;
lean_object* l_Lean_Elab_Term_clearInMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_2354_(lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__26;
extern lean_object* l_Lean_Linter_linter_deprecated;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__0;
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__6;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__19;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_Term_elabArrow___redArg___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_2354_;
static lean_object* l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_mkLetIdDeclView___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1;
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__17;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__9;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__0;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_Binders___hyg_14753_;
static lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
static lean_object* l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_2354_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__0;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10;
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__0;
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandWhereDecls___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0;
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Match_Match_0__Lean_Meta_Match_mkIncorrectNumberOfPatternsMsg___at___Lean_Meta_Match_throwIncorrectNumberOfPatternsAt___at_____private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_spec__2_spec__2_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__1;
static lean_object* l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__2;
static lean_object* l_Lean_Elab_Term_expandForall___closed__4;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__1;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__21;
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_precheckArrow___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveIDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1;
lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__1;
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__5;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___closed__3;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Term_LetConfig_setFrom___closed__9;
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__1;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__9;
lean_object* l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__8;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Term_mkLetIdDeclView___closed__2;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__7;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__0;
lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__3;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__0;
lean_object* l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_universeConstraintsCheckpoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_expandFunBinders_loop___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5;
static lean_object* l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__0;
static lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__15;
static lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5;
static lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3;
static lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__0;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__1;
static lean_object* l_Lean_Elab_Term_quoteAutoTactic___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDecl___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
static lean_object* l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__6;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_2354_;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__2;
static lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__8;
static lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__3;
static lean_object* l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_Binders___hyg_14753_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_mkHole(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkFreshBinderName___at_____private_Lean_Elab_Match_0__Lean_Elab_Term_mkUserNameFor_spec__0___redArg(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_mkIdentFrom(x_1, x_8, x_2);
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
x_12 = l_Lean_mkIdentFrom(x_1, x_10, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(x_1, x_2, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(x_1, x_10, x_6, x_7, x_8);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 10);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_Environment_mainModule(x_8);
lean_dec_ref(x_8);
x_11 = l_Lean_addMacroScope(x_10, x_1, x_9);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 10);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = l_Lean_Environment_mainModule(x_14);
lean_dec_ref(x_14);
x_17 = l_Lean_addMacroScope(x_16, x_1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inst", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isNone(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__1;
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_Core_withFreshMacroScope___redArg(x_10, x_2, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = 0;
x_15 = l_Lean_mkIdentFrom(x_1, x_13, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = 0;
x_19 = l_Lean_mkIdentFrom(x_1, x_16, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(x_1, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_kindOfBinderName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_isImplementationDetail(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_kindOfBinderName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_kindOfBinderName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid auto tactic, antiquotation is not allowed", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("push", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_28; lean_object* x_37; uint8_t x_38; 
x_20 = lean_array_uget(x_5, x_7);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_38 = lean_name_eq(x_4, x_37);
if (x_38 == 0)
{
x_28 = x_38;
goto block_36;
}
else
{
uint8_t x_39; 
x_39 = l_Lean_Syntax_isAntiquotSuffixSplice(x_20);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Syntax_isAntiquotSplice(x_20);
x_28 = x_40;
goto block_36;
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
}
block_27:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1;
x_22 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_20, x_21, x_9, x_10, x_11);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
block_36:
{
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc_ref(x_9);
x_29 = l_Lean_Elab_Term_quoteAutoTactic(x_20, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__2;
lean_inc_ref(x_1);
x_33 = l_Lean_Name_mkStr2(x_1, x_32);
lean_inc(x_2);
x_34 = l_Lean_Expr_const___override(x_33, x_2);
lean_inc_ref(x_3);
x_35 = l_Lean_mkApp3(x_34, x_3, x_8, x_30);
x_12 = x_35;
x_13 = x_31;
goto block_17;
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_29;
}
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_27;
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_7, x_14);
x_7 = x_15;
x_8 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_2);
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_mkStrLit(x_4);
lean_inc_ref(x_2);
x_7 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_1, x_2, x_5);
x_8 = l_Lean_mkAppB(x_2, x_6, x_7);
return x_8;
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Syntax", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Preresolved", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namespace", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__2;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1;
x_3 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nil", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__12;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cons", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__17;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_2);
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__4;
x_12 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_10);
x_13 = l_Lean_Expr_app___override(x_11, x_12);
x_6 = x_13;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__7;
x_17 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_14);
x_18 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__16;
x_19 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__20;
x_20 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_18, x_19, x_15);
x_21 = l_Lean_mkAppB(x_16, x_17, x_20);
x_6 = x_21;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_2);
x_7 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_1, x_2, x_5);
x_8 = l_Lean_mkAppB(x_2, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_quoteAutoTactic___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid auto tactic, tactic is missing", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("empty", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__5;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__3;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__7;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("node", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__9;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SourceInfo", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__13;
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__12;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkAtom", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__16;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__20;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toSubstring", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__22;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__23;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_quoteAutoTactic___closed__25;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_quoteAutoTactic___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__26;
x_2 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_quoteAutoTactic___closed__1;
x_6 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2_spec__2___redArg(x_5, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
x_9 = l_Lean_Syntax_isAntiquot(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_quoteAutoTactic___closed__3;
x_11 = l_Lean_Elab_Term_quoteAutoTactic___closed__4;
x_12 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14;
x_13 = l_Lean_Elab_Term_quoteAutoTactic___closed__8;
x_14 = lean_array_size(x_8);
x_15 = 0;
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(x_11, x_12, x_10, x_7, x_8, x_14, x_15, x_13, x_2, x_3, x_4);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_20 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_21 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_7);
x_22 = l_Lean_mkApp3(x_19, x_20, x_21, x_18);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = l_Lean_Elab_Term_quoteAutoTactic___closed__11;
x_26 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_27 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_7);
x_28 = l_Lean_mkApp3(x_25, x_26, x_27, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_dec(x_7);
return x_16;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_8);
lean_dec(x_7);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1;
x_31 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_1, x_30, x_2, x_3, x_4);
lean_dec(x_1);
return x_31;
}
}
case 2:
{
uint8_t x_32; 
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
x_36 = l_Lean_mkStrLit(x_33);
x_37 = l_Lean_Expr_app___override(x_35, x_36);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Elab_Term_quoteAutoTactic___closed__18;
x_40 = l_Lean_mkStrLit(x_38);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
return x_42;
}
}
default: 
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 3);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Term_quoteAutoTactic___lam__0___boxed), 1, 0);
x_46 = l_Lean_Elab_Term_quoteAutoTactic___closed__21;
x_47 = l_Lean_Elab_Term_quoteAutoTactic___closed__15;
x_48 = l_Lean_Elab_Term_quoteAutoTactic___closed__24;
x_49 = 1;
lean_inc(x_43);
x_50 = l_Lean_Name_toString(x_43, x_49, x_45);
x_51 = l_Lean_mkStrLit(x_50);
x_52 = l_Lean_Expr_app___override(x_48, x_51);
x_53 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_43);
x_54 = l_Lean_Elab_Term_quoteAutoTactic___closed__27;
x_55 = l_Lean_Elab_Term_quoteAutoTactic___closed__28;
x_56 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_54, x_55, x_44);
x_57 = l_Lean_mkApp4(x_46, x_47, x_52, x_53, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_____private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_quoteAutoTactic___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_quoteAutoTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__6;
x_2 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__5;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__4;
x_4 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__3;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoParam", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9;
x_2 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_auto", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_106; lean_object* x_107; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_139; lean_object* x_140; 
x_125 = lean_st_ref_get(x_6, x_7);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_139 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_139);
lean_dec(x_126);
x_140 = l_Lean_Environment_asyncPrefix_x3f(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_box(0);
x_128 = x_141;
goto block_138;
}
else
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_128 = x_142;
goto block_138;
}
block_138:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_st_ref_get(x_6, x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_5, 10);
lean_inc(x_133);
x_134 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__12;
x_135 = l_Lean_Name_append(x_128, x_134);
x_136 = l_Lean_Environment_mainModule(x_132);
lean_dec_ref(x_132);
x_137 = l_Lean_addMacroScope(x_136, x_135, x_133);
x_106 = x_137;
x_107 = x_131;
goto block_124;
}
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_4, 0);
lean_inc(x_143);
lean_dec(x_4);
x_106 = x_143;
x_107 = x_7;
goto block_124;
}
block_105:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_box(0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
x_15 = lean_box(0);
x_16 = 1;
lean_inc(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_19);
x_20 = l_Lean_addDecl(x_19, x_5, x_6, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_st_ref_take(x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 5);
lean_dec(x_27);
lean_inc(x_10);
x_28 = l_Lean_addMeta(x_26, x_10);
x_29 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2;
lean_ctor_set(x_23, 5, x_29);
lean_ctor_set(x_23, 0, x_28);
x_30 = lean_st_ref_set(x_6, x_23, x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_st_ref_take(x_11, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 1);
lean_dec(x_36);
x_37 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7;
lean_ctor_set(x_33, 1, x_37);
x_38 = lean_st_ref_set(x_11, x_33, x_34);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = 1;
x_41 = l_Lean_compileDecl(x_19, x_40, x_5, x_6, x_39);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_10);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 2);
x_52 = lean_ctor_get(x_33, 3);
x_53 = lean_ctor_get(x_33, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_54 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7;
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
x_56 = lean_st_ref_set(x_11, x_55, x_34);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = 1;
x_59 = l_Lean_compileDecl(x_19, x_58, x_5, x_6, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_67 = lean_ctor_get(x_23, 0);
x_68 = lean_ctor_get(x_23, 1);
x_69 = lean_ctor_get(x_23, 2);
x_70 = lean_ctor_get(x_23, 3);
x_71 = lean_ctor_get(x_23, 4);
x_72 = lean_ctor_get(x_23, 6);
x_73 = lean_ctor_get(x_23, 7);
x_74 = lean_ctor_get(x_23, 8);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_23);
lean_inc(x_10);
x_75 = l_Lean_addMeta(x_67, x_10);
x_76 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2;
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_69);
lean_ctor_set(x_77, 3, x_70);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_76);
lean_ctor_set(x_77, 6, x_72);
lean_ctor_set(x_77, 7, x_73);
lean_ctor_set(x_77, 8, x_74);
x_78 = lean_st_ref_set(x_6, x_77, x_24);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_st_ref_take(x_11, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_81, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 3);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_81, 4);
lean_inc_ref(x_86);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_87 = x_81;
} else {
 lean_dec_ref(x_81);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 5, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
x_90 = lean_st_ref_set(x_11, x_89, x_82);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = 1;
x_93 = l_Lean_compileDecl(x_19, x_92, x_5, x_6, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
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
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_10);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_10);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
x_101 = !lean_is_exclusive(x_20);
if (x_101 == 0)
{
return x_20;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_20, 0);
x_103 = lean_ctor_get(x_20, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_20);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
block_124:
{
lean_object* x_108; 
lean_inc_ref(x_5);
x_108 = l_Lean_Elab_Term_quoteAutoTactic(x_1, x_5, x_6, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10;
x_112 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_111, x_5, x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = l_Lean_Elab_Term_quoteAutoTactic___closed__3;
x_116 = lean_unbox(x_113);
lean_dec(x_113);
if (x_116 == 0)
{
x_8 = x_109;
x_9 = x_115;
x_10 = x_106;
x_11 = x_2;
x_12 = x_114;
goto block_105;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_inc(x_109);
x_117 = l_Lean_MessageData_ofExpr(x_109);
x_118 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_111, x_117, x_3, x_2, x_5, x_6, x_114);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec_ref(x_118);
x_8 = x_109;
x_9 = x_115;
x_10 = x_106;
x_11 = x_2;
x_12 = x_119;
goto block_105;
}
}
else
{
uint8_t x_120; 
lean_dec(x_106);
lean_dec(x_6);
lean_dec_ref(x_5);
x_120 = !lean_is_exclusive(x_108);
if (x_120 == 0)
{
return x_108;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_108, 0);
x_122 = lean_ctor_get(x_108, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_108);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___boxed), 7, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_2);
x_9 = l_Lean_Core_withFreshMacroScope___redArg(x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_declareTacticSyntax___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_declareTacticSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_declareTacticSyntax(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binderDefault", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binderTactic", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optParam", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_isNone(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_2, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__1;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__3;
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_10, x_17);
lean_dec(x_10);
x_19 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_18);
x_20 = l_Lean_Elab_Term_declareTacticSyntax___redArg(x_18, x_19, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_st_ref_get(x_6, x_22);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_5, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 10);
lean_inc(x_27);
lean_dec_ref(x_5);
x_28 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_28);
lean_dec(x_25);
x_29 = l_Lean_SourceInfo_fromRef(x_26, x_13);
lean_dec(x_26);
x_30 = l_Lean_Environment_mainModule(x_28);
lean_dec_ref(x_28);
x_31 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5;
x_32 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6;
x_33 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7;
x_34 = l_Lean_addMacroScope(x_30, x_33, x_27);
x_35 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9;
lean_inc(x_29);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_38 = l_Lean_mkIdentFrom(x_18, x_21, x_13);
lean_dec(x_18);
lean_inc(x_29);
x_39 = l_Lean_Syntax_node2(x_29, x_37, x_1, x_38);
x_40 = l_Lean_Syntax_node2(x_29, x_31, x_36, x_39);
lean_ctor_set(x_23, 0, x_40);
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_ctor_get(x_5, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 10);
lean_inc(x_44);
lean_dec_ref(x_5);
x_45 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_45);
lean_dec(x_41);
x_46 = l_Lean_SourceInfo_fromRef(x_43, x_13);
lean_dec(x_43);
x_47 = l_Lean_Environment_mainModule(x_45);
lean_dec_ref(x_45);
x_48 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5;
x_49 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6;
x_50 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7;
x_51 = l_Lean_addMacroScope(x_47, x_50, x_44);
x_52 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9;
lean_inc(x_46);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_52);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_55 = l_Lean_mkIdentFrom(x_18, x_21, x_13);
lean_dec(x_18);
lean_inc(x_46);
x_56 = l_Lean_Syntax_node2(x_46, x_54, x_1, x_55);
x_57 = l_Lean_Syntax_node2(x_46, x_48, x_53, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_20);
if (x_59 == 0)
{
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_20, 0);
x_61 = lean_ctor_get(x_20, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_20);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
x_63 = lean_st_ref_get(x_6, x_7);
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_5, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 10);
lean_inc(x_67);
lean_dec_ref(x_5);
x_68 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_68);
lean_dec(x_65);
x_69 = lean_unsigned_to_nat(1u);
x_70 = l_Lean_Syntax_getArg(x_10, x_69);
lean_dec(x_10);
x_71 = l_Lean_SourceInfo_fromRef(x_66, x_8);
lean_dec(x_66);
x_72 = l_Lean_Environment_mainModule(x_68);
lean_dec_ref(x_68);
x_73 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5;
x_74 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11;
x_75 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12;
x_76 = l_Lean_addMacroScope(x_72, x_75, x_67);
x_77 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14;
lean_inc(x_71);
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_71);
x_80 = l_Lean_Syntax_node2(x_71, x_79, x_1, x_70);
x_81 = l_Lean_Syntax_node2(x_71, x_73, x_78, x_80);
lean_ctor_set(x_63, 0, x_81);
return x_63;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_82 = lean_ctor_get(x_63, 0);
x_83 = lean_ctor_get(x_63, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_63);
x_84 = lean_ctor_get(x_5, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_5, 10);
lean_inc(x_85);
lean_dec_ref(x_5);
x_86 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_86);
lean_dec(x_82);
x_87 = lean_unsigned_to_nat(1u);
x_88 = l_Lean_Syntax_getArg(x_10, x_87);
lean_dec(x_10);
x_89 = l_Lean_SourceInfo_fromRef(x_84, x_8);
lean_dec(x_84);
x_90 = l_Lean_Environment_mainModule(x_86);
lean_dec_ref(x_86);
x_91 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5;
x_92 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11;
x_93 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12;
x_94 = l_Lean_addMacroScope(x_90, x_93, x_85);
x_95 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14;
lean_inc(x_89);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_95);
x_97 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_89);
x_98 = l_Lean_Syntax_node2(x_89, x_97, x_1, x_88);
x_99 = l_Lean_Syntax_node2(x_89, x_91, x_96, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_83);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_7);
return x_101;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("identifier or `_` expected", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
lean_dec_ref(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_23; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_13);
x_31 = l_Lean_Syntax_getKind(x_13);
x_32 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2;
x_33 = lean_name_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_35 = lean_name_eq(x_31, x_34);
lean_dec(x_31);
x_23 = x_35;
goto block_30;
}
else
{
lean_dec(x_31);
x_23 = x_33;
goto block_30;
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_10 = x_17;
goto _start;
}
block_30:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec_ref(x_15);
x_24 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1;
x_25 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_13, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
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
x_16 = x_13;
x_17 = x_10;
goto block_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
lean_dec_ref(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_23; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_13);
x_31 = l_Lean_Syntax_getKind(x_13);
x_32 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2;
x_33 = lean_name_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_35 = lean_name_eq(x_31, x_34);
lean_dec(x_31);
x_23 = x_35;
goto block_30;
}
else
{
lean_dec(x_31);
x_23 = x_33;
goto block_30;
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_15, x_2, x_16);
x_21 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(x_1, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_21;
}
block_30:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec_ref(x_15);
x_24 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1;
x_25 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_13, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
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
x_16 = x_13;
x_17 = x_10;
goto block_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = l_Lean_Syntax_getArgs(x_1);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_14, x_1);
x_21 = 2;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_19, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_14, x_1);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_19, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_5, x_4);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_15);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderType(x_15, x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_20 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg(x_19, x_2, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_uset(x_5, x_4, x_23);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = lean_array_uset(x_24, x_4, x_26);
x_4 = x_28;
x_5 = x_29;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
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
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explicitBinder", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implicitBinder", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instBinder", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_111; 
lean_inc(x_1);
x_9 = l_Lean_Syntax_getKind(x_1);
x_111 = l_Lean_Syntax_isIdent(x_1);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_113 = lean_name_eq(x_9, x_112);
x_10 = x_113;
goto block_110;
}
else
{
x_10 = x_111;
goto block_110;
}
block_110:
{
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1;
x_12 = lean_name_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__3;
x_14 = lean_name_eq(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__5;
x_16 = lean_name_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__7;
x_18 = lean_name_eq(x_9, x_17);
lean_dec(x_9);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg(x_21, x_6, x_7, x_8);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_27 = 3;
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8;
x_30 = lean_array_push(x_29, x_28);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_unsigned_to_nat(2u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
lean_dec(x_1);
x_35 = 3;
lean_inc(x_31);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_35);
x_37 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8;
x_38 = lean_array_push(x_37, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_46 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Syntax_getArg(x_1, x_49);
lean_dec(x_1);
x_51 = lean_array_size(x_47);
x_52 = 0;
x_53 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(x_50, x_51, x_52, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_50);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_9);
x_58 = lean_unsigned_to_nat(1u);
x_59 = l_Lean_Syntax_getArg(x_1, x_58);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_60 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_unsigned_to_nat(2u);
x_64 = l_Lean_Syntax_getArg(x_1, x_63);
lean_dec(x_1);
x_65 = lean_array_size(x_61);
x_66 = 0;
x_67 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(x_64, x_65, x_66, x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_64);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
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
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_9);
x_72 = lean_unsigned_to_nat(1u);
x_73 = l_Lean_Syntax_getArg(x_1, x_72);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_74 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_unsigned_to_nat(2u);
x_78 = l_Lean_Syntax_getArg(x_1, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
lean_dec(x_1);
x_81 = lean_array_size(x_75);
x_82 = 0;
x_83 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(x_78, x_80, x_81, x_82, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_76);
lean_dec_ref(x_2);
lean_dec(x_80);
lean_dec(x_78);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_74);
if (x_84 == 0)
{
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
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
lean_object* x_88; 
lean_dec(x_9);
lean_inc(x_1);
x_88 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = 0;
x_92 = l_Lean_mkHole(x_1, x_91);
x_93 = 0;
x_94 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_93);
x_95 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8;
x_96 = lean_array_push(x_95, x_94);
lean_ctor_set(x_88, 0, x_96);
return x_88;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = 0;
x_100 = l_Lean_mkHole(x_1, x_99);
x_101 = 0;
x_102 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_97);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_101);
x_103 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8;
x_104 = lean_array_push(x_103, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_98);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_88);
if (x_106 == 0)
{
return x_88;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_88, 0);
x_108 = lean_ctor_get(x_88, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_88);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews_spec__2(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to infer ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to infer universe levels in ", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type of binder `", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binder type", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_28; uint8_t x_29; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_28 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_29 = l_Lean_Name_hasMacroScopes(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__7;
x_31 = l_Lean_MessageData_ofName(x_28);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__9;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_8 = x_34;
goto block_27;
}
else
{
lean_object* x_35; 
lean_dec(x_28);
x_35 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__11;
x_8 = x_35;
goto block_27;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__1;
lean_inc_ref(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_6);
x_13 = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(x_1, x_6, x_12, x_3, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_11);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(x_1, x_6, x_19, x_3, x_4, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(x_1, x_6, x_25, x_3, x_4, x_21);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg(x_1, x_2, x_4, x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = 1;
x_14 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_2, x_10, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid binder name '", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', it must be atomic", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_Syntax_getId(x_9);
x_11 = lean_erase_macro_scopes(x_10);
x_12 = l_Lean_Name_isAtomic(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1;
x_14 = l_Lean_MessageData_ofName(x_11);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_9, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkBinderAnnotations", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_2354_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_2354_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check whether type is a class instance whenever the binder annotation `[...]` is used", 85, 85);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_2354_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_2354_;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_2354_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_2354_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_2354_;
x_3 = l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_2354_;
x_4 = l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_2354_;
x_5 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_2);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid parametric local instance, parameter with type", 54, 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndoes not have forward dependencies, type class resolution cannot use this kind of local instance because it will not be able to infer a value for this parameter.", 162, 162);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_whnf(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_27; uint8_t x_28; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 8);
lean_dec(x_10);
lean_inc_ref(x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0___boxed), 9, 1);
lean_closure_set(x_16, 0, x_14);
x_27 = 3;
x_28 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_15, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_expr_has_loose_bvar(x_14, x_29);
lean_dec_ref(x_14);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_16);
lean_dec(x_12);
x_31 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__1;
x_32 = l_Lean_indentExpr(x_13);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__3;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_36;
}
else
{
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_11;
goto block_26;
}
}
else
{
lean_dec_ref(x_14);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_11;
goto block_26;
}
block_26:
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_12, x_15, x_13, x_16, x_24, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_25;
}
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_9, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_15 = l_Lean_Elab_Term_addLocalVarInfo(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_array_push(x_4, x_19);
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(x_5, x_6, x_18, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = l_Lean_Syntax_getId(x_1);
x_14 = l_Lean_Elab_Term_kindOfBinderName(x_13);
x_15 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop_spec__0___redArg(x_13, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid binder annotation, type is not a class instance", 55, 55);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Use the command `set_option checkBinderAnnotations false` to disable the check", 78, 78);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__4;
x_2 = l_Lean_MessageData_note(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_checkBinderAnnotations;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec_ref(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_3);
lean_inc_ref(x_9);
lean_inc_ref(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_20);
x_22 = l_Lean_Elab_Term_elabType(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_62; uint8_t x_86; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_inc(x_23);
x_25 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg(x_23, x_15, x_6, x_7, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
lean_inc(x_19);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0___boxed), 14, 6);
lean_closure_set(x_28, 0, x_18);
lean_closure_set(x_28, 1, x_3);
lean_closure_set(x_28, 2, x_19);
lean_closure_set(x_28, 3, x_4);
lean_closure_set(x_28, 4, x_1);
lean_closure_set(x_28, 5, x_2);
x_86 = l_Lean_BinderInfo_isInstImplicit(x_21);
if (x_86 == 0)
{
x_62 = x_86;
goto block_85;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_9, 2);
lean_inc(x_87);
x_88 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__6;
x_89 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_87, x_88);
lean_dec(x_87);
x_62 = x_89;
goto block_85;
}
block_61:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_33, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_33, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_33, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 7);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 8);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 9);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 10);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_33, sizeof(void*)*13);
x_48 = lean_ctor_get(x_33, 11);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_33, sizeof(void*)*13 + 1);
x_50 = lean_ctor_get(x_33, 12);
lean_inc_ref(x_50);
x_51 = l_Lean_replaceRef(x_20, x_41);
lean_dec(x_41);
lean_dec(x_20);
x_52 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_37);
lean_ctor_set(x_52, 2, x_38);
lean_ctor_set(x_52, 3, x_39);
lean_ctor_set(x_52, 4, x_40);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set(x_52, 6, x_42);
lean_ctor_set(x_52, 7, x_43);
lean_ctor_set(x_52, 8, x_44);
lean_ctor_set(x_52, 9, x_45);
lean_ctor_set(x_52, 10, x_46);
lean_ctor_set(x_52, 11, x_48);
lean_ctor_set(x_52, 12, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*13, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*13 + 1, x_49);
lean_inc(x_34);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_23);
x_53 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters(x_23, x_29, x_30, x_31, x_32, x_52, x_34, x_35);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(x_19, x_21, x_23, x_28, x_54, x_29, x_30, x_31, x_32, x_33, x_34, x_55);
lean_dec(x_54);
lean_dec(x_19);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_23);
lean_dec(x_19);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
block_85:
{
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_27);
lean_dec(x_20);
x_63 = lean_box(0);
x_64 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(x_19, x_21, x_23, x_28, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_19);
return x_64;
}
else
{
lean_object* x_65; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_23);
x_65 = l_Lean_Meta_isClass_x3f(x_23, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec_ref(x_28);
lean_dec(x_19);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__1;
x_69 = l_Lean_indentExpr(x_23);
if (lean_is_scalar(x_27)) {
 x_70 = lean_alloc_ctor(7, 2, 0);
} else {
 x_70 = x_27;
 lean_ctor_set_tag(x_70, 7);
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__5;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_20, x_74, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_20);
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
lean_object* x_80; 
lean_dec(x_66);
lean_dec(x_27);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_dec_ref(x_65);
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_80;
goto block_61;
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_81 = !lean_is_exclusive(x_65);
if (x_81 == 0)
{
return x_65;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_65, 0);
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_65);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_22);
if (x_90 == 0)
{
return x_22;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_22, 0);
x_92 = lean_ctor_get(x_22, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_22);
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
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___lam__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg(x_1, x_3, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_5);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg___boxed), 11, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_20);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews___redArg(x_17, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0;
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux_loop___redArg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0;
x_13 = lean_apply_8(x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_isEmpty___redArg(x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBindersEx___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
x_13 = l_Lean_Elab_Term_universeConstraintsCheckpoint___redArg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBindersEx___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBindersEx___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Elab_Term_elabBindersEx___redArg___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(x_10, x_11, x_2);
x_13 = lean_apply_8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___redArg___lam__0), 9, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_Lean_Elab_Term_elabBindersEx___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBinders___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_elabBinders_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_1, x_3, x_11);
x_13 = lean_apply_8(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabBinder___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
x_12 = l_Lean_Elab_Term_elabBinder___redArg___closed__0;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Lean_Elab_Term_elabBinders___redArg(x_13, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBinder___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabBinder___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabBinder___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type ascription", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandSimpleBinderWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_26; uint8_t x_27; 
x_26 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
lean_inc(x_2);
x_27 = l_Lean_Syntax_isOfKind(x_2, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Syntax_isIdent(x_2);
x_5 = x_28;
goto block_25;
}
else
{
x_5 = x_27;
goto block_25;
}
block_25:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__0;
x_7 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_6, x_3, x_4);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_3, 5);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1;
x_12 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1;
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_10);
x_15 = l_Lean_Syntax_node1(x_10, x_14, x_2);
x_16 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
lean_inc(x_10);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_10);
x_18 = l_Lean_Syntax_node2(x_10, x_14, x_17, x_1);
x_19 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_10);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4;
lean_inc(x_10);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Syntax_node5(x_10, x_11, x_13, x_15, x_18, x_20, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
lean_inc_ref(x_5);
x_10 = lean_apply_3(x_1, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_14, x_3, x_11);
x_3 = x_16;
x_4 = x_17;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandForall___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeSpec", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandForall___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Elab_Term_expandForall___closed__0;
x_5 = l_Lean_Elab_Term_expandForall___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_matchesNull(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_Elab_Term_expandForall___closed__3;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = l_Lean_Syntax_getArg(x_1, x_8);
x_19 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_20 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSimpleBinderWithType), 4, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_array_size(x_20);
x_23 = 0;
lean_inc_ref(x_2);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(x_21, x_22, x_23, x_20, x_2, x_3);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_2, 5);
lean_inc(x_27);
lean_dec_ref(x_2);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
lean_dec(x_1);
x_30 = 0;
x_31 = l_Lean_SourceInfo_fromRef(x_27, x_30);
lean_dec(x_27);
lean_inc(x_31);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
x_33 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_34 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_35 = l_Array_append___redArg(x_34, x_26);
lean_dec(x_26);
lean_inc(x_31);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
lean_inc(x_31);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
x_38 = l_Lean_Elab_Term_expandForall___closed__4;
lean_inc(x_31);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Syntax_node5(x_31, x_5, x_32, x_36, x_37, x_39, x_29);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_ctor_get(x_2, 5);
lean_inc(x_43);
lean_dec_ref(x_2);
x_44 = lean_unsigned_to_nat(4u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
lean_dec(x_1);
x_46 = 0;
x_47 = l_Lean_SourceInfo_fromRef(x_43, x_46);
lean_dec(x_43);
lean_inc(x_47);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_50 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_51 = l_Array_append___redArg(x_50, x_41);
lean_dec(x_41);
lean_inc(x_47);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_51);
lean_inc(x_47);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
x_54 = l_Lean_Elab_Term_expandForall___closed__4;
lean_inc(x_47);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Syntax_node5(x_47, x_5, x_48, x_52, x_53, x_55, x_45);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_42);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
return x_24;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandForall", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0;
x_3 = l_Lean_Elab_Term_expandForall___closed__1;
x_4 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandForall), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(264u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(268u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(41u);
x_4 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = lean_unsigned_to_nat(264u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(264u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(45u);
x_4 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2;
x_3 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Elab_Term_elabType(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 0;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_3, x_12, x_14, x_2, x_2, x_15, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_16;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_expandForall___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_matchesNull(x_14, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(4u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = lean_box(x_15);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_24 = l_Lean_Elab_Term_elabBinders___redArg(x_23, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabForall___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Elab_Term_elabForall___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabForall", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_expandForall___closed__1;
x_4 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_unsigned_to_nat(270u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(276u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(30u);
x_4 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(34u);
x_2 = lean_unsigned_to_nat(270u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = lean_unsigned_to_nat(270u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(34u);
x_4 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2;
x_3 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckArrow___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arrow", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckArrow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_precheckArrow___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_precheckArrow___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Quotation_precheckAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckArrow", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0;
x_3 = l_Lean_Elab_Term_precheckArrow___closed__1;
x_4 = l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_precheckArrow), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabArrow___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_precheckArrow___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Elab_Term_elabType(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
x_19 = l_Lean_Elab_Term_elabType(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_ref_get(x_7, x_21);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_6, 10);
lean_inc(x_26);
lean_dec_ref(x_6);
x_27 = l_Lean_Elab_Term_elabArrow___redArg___closed__1;
x_28 = l_Lean_Environment_mainModule(x_25);
lean_dec_ref(x_25);
x_29 = l_Lean_addMacroScope(x_28, x_27, x_26);
x_30 = 0;
x_31 = l_Lean_Expr_forallE___override(x_29, x_15, x_20, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_6, 10);
lean_inc(x_35);
lean_dec_ref(x_6);
x_36 = l_Lean_Elab_Term_elabArrow___redArg___closed__1;
x_37 = l_Lean_Environment_mainModule(x_34);
lean_dec_ref(x_34);
x_38 = l_Lean_addMacroScope(x_37, x_36, x_35);
x_39 = 0;
x_40 = l_Lean_Expr_forallE___override(x_38, x_15, x_20, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_19;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabArrow___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabArrow", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_precheckArrow___closed__1;
x_4 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow___boxed), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(27u);
x_2 = lean_unsigned_to_nat(285u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(292u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(27u);
x_4 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(285u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(40u);
x_2 = lean_unsigned_to_nat(285u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(40u);
x_2 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(31u);
x_4 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1;
x_3 = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l_Lean_Elab_Term_elabType(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_2, x_11, x_13, x_14, x_14, x_15, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_16;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___redArg___lam__0), 9, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Term_elabBinder___redArg___closed__0;
x_15 = lean_array_push(x_14, x_10);
x_16 = l_Lean_Elab_Term_elabBinders___redArg(x_15, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabDepArrow___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabDepArrow___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
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
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depArrow", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabDepArrow", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__1;
x_4 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The dependent arrow. `(x : α) → β` is equivalent to `∀ x : α, β`, but we usually\nreserve the latter for propositions. Also written as `Π x : α, β` (the \"Pi-type\")\nin the literature. ", 193, 182);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3;
x_3 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3___closed__0;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_unsigned_to_nat(298u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(38u);
x_2 = lean_unsigned_to_nat(303u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(38u);
x_2 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__1;
x_3 = lean_unsigned_to_nat(30u);
x_4 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(34u);
x_2 = lean_unsigned_to_nat(298u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(298u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__4;
x_3 = lean_unsigned_to_nat(34u);
x_4 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__5;
x_2 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3;
x_3 = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
lean_inc_ref(x_6);
x_12 = lean_apply_3(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_array_push(x_5, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
x_7 = x_20;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0___boxed), 3, 0);
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_7 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_20 = lean_array_push(x_19, x_18);
lean_ctor_set(x_8, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_23 = lean_array_push(x_22, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_27 = x_8;
} else {
 lean_dec_ref(x_8);
 x_27 = lean_box(0);
}
x_28 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_29 = lean_array_push(x_28, x_26);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
x_34 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(x_33, x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec_ref(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
lean_dec(x_1);
x_46 = l_Lean_Syntax_getArgs(x_45);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_48 = lean_array_push(x_47, x_43);
x_49 = lean_array_size(x_46);
x_50 = 0;
x_51 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(x_4, x_46, x_49, x_50, x_48, x_2, x_42);
lean_dec_ref(x_46);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_ctor_set(x_2, 0, x_8);
x_9 = l_Lean_addMacroScope(x_5, x_6, x_4);
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
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_11, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = l_Lean_addMacroScope(x_13, x_14, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_mkIdentFrom(x_1, x_7, x_2);
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
x_11 = l_Lean_mkIdentFrom(x_1, x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_mkExplicitBinder(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 0;
x_10 = l_Lean_mkHole(x_1, x_9);
x_11 = l_Lean_Elab_Term_mkExplicitBinder(x_6, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc_ref(x_4);
x_9 = l_Lean_Macro_resolveGlobalName(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = 1;
x_14 = l_List_isEmpty___redArg(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_4);
x_15 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
if (x_6 == 0)
{
size_t x_16; size_t x_17; 
lean_free_object(x_9);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_4);
x_19 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = 1;
x_23 = l_List_isEmpty___redArg(x_20);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_4);
x_24 = lean_box(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
if (x_6 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_2 = x_27;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_4);
x_29 = lean_box(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec_ref(x_4);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_4);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("match", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchDiscr", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("with", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchAlts", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchAlt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("|", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=>", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_10 = 0;
lean_inc_ref(x_8);
x_11 = l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(x_1, x_10, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = l_Lean_mkHole(x_1, x_10);
lean_inc(x_13);
x_18 = l_Lean_Elab_Term_mkExplicitBinder(x_13, x_17);
x_19 = lean_array_push(x_3, x_18);
lean_inc_ref(x_8);
x_20 = l_Lean_Elab_Term_expandFunBinders_loop(x_4, x_5, x_16, x_19, x_8, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 5);
lean_inc(x_30);
lean_dec_ref(x_8);
x_31 = l_Lean_SourceInfo_fromRef(x_30, x_10);
lean_dec(x_30);
x_32 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_33 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_31);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_32);
lean_ctor_set(x_11, 0, x_31);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_35 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_31);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3;
lean_inc_ref(x_36);
lean_inc(x_31);
x_38 = l_Lean_Syntax_node2(x_31, x_37, x_36, x_13);
lean_inc(x_31);
x_39 = l_Lean_Syntax_node1(x_31, x_34, x_38);
x_40 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_31);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
x_43 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8;
x_44 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_31);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_31);
x_46 = l_Lean_Syntax_node1(x_31, x_34, x_1);
lean_inc(x_31);
x_47 = l_Lean_Syntax_node1(x_31, x_34, x_46);
x_48 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_31);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_31);
x_50 = l_Lean_Syntax_node4(x_31, x_43, x_45, x_47, x_49, x_28);
lean_inc(x_31);
x_51 = l_Lean_Syntax_node1(x_31, x_34, x_50);
lean_inc(x_31);
x_52 = l_Lean_Syntax_node1(x_31, x_42, x_51);
lean_inc_ref(x_36);
x_53 = l_Lean_Syntax_node6(x_31, x_33, x_11, x_36, x_36, x_39, x_41, x_52);
x_54 = lean_box(x_6);
lean_ctor_set(x_22, 1, x_54);
lean_ctor_set(x_22, 0, x_53);
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
lean_dec(x_22);
x_56 = lean_ctor_get(x_8, 5);
lean_inc(x_56);
lean_dec_ref(x_8);
x_57 = l_Lean_SourceInfo_fromRef(x_56, x_10);
lean_dec(x_56);
x_58 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_59 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_57);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_58);
lean_ctor_set(x_11, 0, x_57);
x_60 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_61 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_57);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_61);
x_63 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3;
lean_inc_ref(x_62);
lean_inc(x_57);
x_64 = l_Lean_Syntax_node2(x_57, x_63, x_62, x_13);
lean_inc(x_57);
x_65 = l_Lean_Syntax_node1(x_57, x_60, x_64);
x_66 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_57);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
x_69 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8;
x_70 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_57);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_57);
x_72 = l_Lean_Syntax_node1(x_57, x_60, x_1);
lean_inc(x_57);
x_73 = l_Lean_Syntax_node1(x_57, x_60, x_72);
x_74 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_57);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_57);
x_76 = l_Lean_Syntax_node4(x_57, x_69, x_71, x_73, x_75, x_55);
lean_inc(x_57);
x_77 = l_Lean_Syntax_node1(x_57, x_60, x_76);
lean_inc(x_57);
x_78 = l_Lean_Syntax_node1(x_57, x_68, x_77);
lean_inc_ref(x_62);
x_79 = l_Lean_Syntax_node6(x_57, x_59, x_11, x_62, x_62, x_65, x_67, x_78);
x_80 = lean_box(x_6);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_21, 1, x_81);
return x_20;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_82 = lean_ctor_get(x_21, 0);
lean_inc(x_82);
lean_dec(x_21);
x_83 = lean_ctor_get(x_22, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_84 = x_22;
} else {
 lean_dec_ref(x_22);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_8, 5);
lean_inc(x_85);
lean_dec_ref(x_8);
x_86 = l_Lean_SourceInfo_fromRef(x_85, x_10);
lean_dec(x_85);
x_87 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_88 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_86);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_87);
lean_ctor_set(x_11, 0, x_86);
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_90 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_86);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_90);
x_92 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3;
lean_inc_ref(x_91);
lean_inc(x_86);
x_93 = l_Lean_Syntax_node2(x_86, x_92, x_91, x_13);
lean_inc(x_86);
x_94 = l_Lean_Syntax_node1(x_86, x_89, x_93);
x_95 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_86);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
x_98 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8;
x_99 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_86);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_86);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_86);
x_101 = l_Lean_Syntax_node1(x_86, x_89, x_1);
lean_inc(x_86);
x_102 = l_Lean_Syntax_node1(x_86, x_89, x_101);
x_103 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_86);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_86);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_86);
x_105 = l_Lean_Syntax_node4(x_86, x_98, x_100, x_102, x_104, x_83);
lean_inc(x_86);
x_106 = l_Lean_Syntax_node1(x_86, x_89, x_105);
lean_inc(x_86);
x_107 = l_Lean_Syntax_node1(x_86, x_97, x_106);
lean_inc_ref(x_91);
x_108 = l_Lean_Syntax_node6(x_86, x_88, x_11, x_91, x_91, x_94, x_96, x_107);
x_109 = lean_box(x_6);
if (lean_is_scalar(x_84)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_84;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_82);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_20, 0, x_111);
return x_20;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_112 = lean_ctor_get(x_20, 1);
lean_inc(x_112);
lean_dec(x_20);
x_113 = lean_ctor_get(x_21, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_114 = x_21;
} else {
 lean_dec_ref(x_21);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_22, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_116 = x_22;
} else {
 lean_dec_ref(x_22);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_8, 5);
lean_inc(x_117);
lean_dec_ref(x_8);
x_118 = l_Lean_SourceInfo_fromRef(x_117, x_10);
lean_dec(x_117);
x_119 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_120 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_118);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_119);
lean_ctor_set(x_11, 0, x_118);
x_121 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_122 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_118);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_122);
x_124 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3;
lean_inc_ref(x_123);
lean_inc(x_118);
x_125 = l_Lean_Syntax_node2(x_118, x_124, x_123, x_13);
lean_inc(x_118);
x_126 = l_Lean_Syntax_node1(x_118, x_121, x_125);
x_127 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_118);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_118);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
x_130 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8;
x_131 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_118);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_118);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_118);
x_133 = l_Lean_Syntax_node1(x_118, x_121, x_1);
lean_inc(x_118);
x_134 = l_Lean_Syntax_node1(x_118, x_121, x_133);
x_135 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_118);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_118);
x_137 = l_Lean_Syntax_node4(x_118, x_130, x_132, x_134, x_136, x_115);
lean_inc(x_118);
x_138 = l_Lean_Syntax_node1(x_118, x_121, x_137);
lean_inc(x_118);
x_139 = l_Lean_Syntax_node1(x_118, x_129, x_138);
lean_inc_ref(x_123);
x_140 = l_Lean_Syntax_node6(x_118, x_120, x_11, x_123, x_123, x_126, x_128, x_139);
x_141 = lean_box(x_6);
if (lean_is_scalar(x_116)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_116;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
if (lean_is_scalar(x_114)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_114;
}
lean_ctor_set(x_143, 0, x_113);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_112);
return x_144;
}
}
else
{
lean_free_object(x_11);
lean_dec(x_13);
lean_dec_ref(x_8);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_11, 0);
x_146 = lean_ctor_get(x_11, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_11);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_add(x_2, x_147);
x_149 = l_Lean_mkHole(x_1, x_10);
lean_inc(x_145);
x_150 = l_Lean_Elab_Term_mkExplicitBinder(x_145, x_149);
x_151 = lean_array_push(x_3, x_150);
lean_inc_ref(x_8);
x_152 = l_Lean_Elab_Term_expandFunBinders_loop(x_4, x_5, x_148, x_151, x_8, x_146);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_160 = x_154;
} else {
 lean_dec_ref(x_154);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_8, 5);
lean_inc(x_161);
lean_dec_ref(x_8);
x_162 = l_Lean_SourceInfo_fromRef(x_161, x_10);
lean_dec(x_161);
x_163 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_164 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_162);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
x_166 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_167 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_162);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_166);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3;
lean_inc_ref(x_168);
lean_inc(x_162);
x_170 = l_Lean_Syntax_node2(x_162, x_169, x_168, x_145);
lean_inc(x_162);
x_171 = l_Lean_Syntax_node1(x_162, x_166, x_170);
x_172 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_162);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
x_175 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8;
x_176 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_162);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_162);
lean_ctor_set(x_177, 1, x_176);
lean_inc(x_162);
x_178 = l_Lean_Syntax_node1(x_162, x_166, x_1);
lean_inc(x_162);
x_179 = l_Lean_Syntax_node1(x_162, x_166, x_178);
x_180 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_162);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_162);
lean_ctor_set(x_181, 1, x_180);
lean_inc(x_162);
x_182 = l_Lean_Syntax_node4(x_162, x_175, x_177, x_179, x_181, x_159);
lean_inc(x_162);
x_183 = l_Lean_Syntax_node1(x_162, x_166, x_182);
lean_inc(x_162);
x_184 = l_Lean_Syntax_node1(x_162, x_174, x_183);
lean_inc_ref(x_168);
x_185 = l_Lean_Syntax_node6(x_162, x_164, x_165, x_168, x_168, x_171, x_173, x_184);
x_186 = lean_box(x_6);
if (lean_is_scalar(x_160)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_160;
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
if (lean_is_scalar(x_158)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_158;
}
lean_ctor_set(x_188, 0, x_157);
lean_ctor_set(x_188, 1, x_187);
if (lean_is_scalar(x_156)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_156;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_155);
return x_189;
}
else
{
lean_dec(x_145);
lean_dec_ref(x_8);
lean_dec(x_1);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeAscription", 14, 14);
return x_1;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_3);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; lean_object* x_22; lean_object* x_26; 
x_13 = lean_array_fget(x_1, x_3);
lean_inc(x_13);
x_26 = l_Lean_Syntax_getKind(x_13);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_quoteAutoTactic___closed__19;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
else
{
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
case 1:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_37);
lean_dec(x_32);
x_38 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_39 = lean_string_dec_eq(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_41 = lean_string_dec_eq(x_36, x_40);
lean_dec_ref(x_36);
if (x_41 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_34);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_43 = lean_string_dec_eq(x_35, x_42);
lean_dec_ref(x_35);
if (x_43 == 0)
{
lean_dec_ref(x_34);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2;
x_45 = lean_string_dec_eq(x_34, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4;
x_47 = lean_string_dec_eq(x_34, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6;
x_49 = lean_string_dec_eq(x_34, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0;
x_51 = lean_string_dec_eq(x_34, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3;
x_53 = lean_string_dec_eq(x_34, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Elab_Term_expandFunBinders_loop___closed__0;
x_55 = lean_string_dec_eq(x_34, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
x_57 = lean_string_dec_eq(x_34, x_56);
lean_dec_ref(x_34);
if (x_57 == 0)
{
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = l_Lean_Syntax_getArg(x_13, x_58);
x_79 = lean_unsigned_to_nat(3u);
x_80 = l_Lean_Syntax_getArg(x_13, x_79);
x_81 = l_Lean_Syntax_getOptional_x3f(x_80);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = l_Lean_mkHole(x_13, x_55);
x_60 = x_82;
goto block_78;
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_60 = x_83;
goto block_78;
}
block_78:
{
lean_object* x_61; 
lean_inc_ref(x_5);
x_61 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_59, x_5, x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_box(0);
x_65 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_64, x_5, x_63);
lean_dec(x_3);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_13);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec_ref(x_61);
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_nat_add(x_3, x_58);
lean_dec(x_3);
x_69 = lean_array_size(x_67);
x_70 = 0;
x_71 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(x_60, x_69, x_70, x_67);
x_72 = l_Array_append___redArg(x_4, x_71);
lean_dec_ref(x_71);
x_3 = x_68;
x_4 = x_72;
x_6 = x_66;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
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
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_34);
x_84 = lean_unsigned_to_nat(1u);
x_85 = l_Lean_Syntax_getArg(x_13, x_84);
lean_inc_ref(x_5);
x_86 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f(x_85, x_5, x_6);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
x_89 = lean_box(0);
x_90 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_89, x_5, x_88);
lean_dec(x_3);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec_ref(x_86);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_array_get_size(x_92);
x_113 = lean_nat_dec_lt(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_112);
x_114 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_55, x_53, x_113, x_5, x_91);
x_93 = x_114;
goto block_110;
}
else
{
if (x_113 == 0)
{
lean_object* x_115; 
lean_dec(x_112);
x_115 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_55, x_53, x_113, x_5, x_91);
x_93 = x_115;
goto block_110;
}
else
{
size_t x_116; size_t x_117; lean_object* x_118; 
x_116 = 0;
x_117 = lean_usize_of_nat(x_112);
lean_dec(x_112);
lean_inc_ref(x_5);
x_118 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(x_92, x_116, x_117, x_5, x_91);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = lean_unbox(x_119);
lean_dec(x_119);
x_122 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_55, x_53, x_121, x_5, x_120);
x_93 = x_122;
goto block_110;
}
else
{
x_93 = x_118;
goto block_110;
}
}
}
block_110:
{
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec_ref(x_93);
x_97 = lean_box(0);
x_98 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_97, x_5, x_96);
lean_dec(x_3);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec_ref(x_93);
x_100 = lean_nat_add(x_3, x_84);
lean_dec(x_3);
x_101 = lean_array_size(x_92);
x_102 = 0;
x_103 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(x_13, x_101, x_102, x_92);
lean_dec(x_13);
x_104 = l_Array_append___redArg(x_4, x_103);
lean_dec_ref(x_103);
x_3 = x_100;
x_4 = x_104;
x_6 = x_99;
goto _start;
}
}
else
{
uint8_t x_106; 
lean_dec(x_92);
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_93);
if (x_106 == 0)
{
return x_93;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_93, 0);
x_108 = lean_ctor_get(x_93, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_93);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_86);
if (x_123 == 0)
{
return x_86;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_86, 0);
x_125 = lean_ctor_get(x_86, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_86);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
lean_dec_ref(x_34);
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
else
{
lean_dec_ref(x_34);
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
else
{
lean_dec_ref(x_34);
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
else
{
lean_dec_ref(x_34);
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
else
{
lean_dec_ref(x_34);
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
}
else
{
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
}
default: 
{
lean_dec(x_27);
lean_dec(x_26);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
}
}
else
{
lean_dec(x_26);
x_21 = x_5;
x_22 = x_6;
goto block_25;
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_array_push(x_4, x_13);
x_3 = x_17;
x_4 = x_18;
x_5 = x_14;
x_6 = x_15;
goto _start;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_13, x_3, x_4, x_1, x_2, x_8, x_23, x_21, x_22);
lean_dec(x_3);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandFunBinders_loop_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandFunBinders_loop_spec__4(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Elab_Term_expandFunBinders_loop___lam__1(x_6, x_7, x_8, x_4, x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_7 = l_Lean_Elab_Term_expandFunBinders_loop(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandFunBinders(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
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
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_18 = l_Lean_Meta_whnfForall(x_17, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_22);
lean_dec(x_19);
x_23 = l_Lean_Meta_isExprDefEq(x_2, x_21, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_expr_instantiate1(x_22, x_1);
lean_dec_ref(x_22);
lean_ctor_set(x_9, 0, x_26);
lean_ctor_set(x_23, 0, x_3);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_expr_instantiate1(x_22, x_1);
lean_dec_ref(x_22);
lean_ctor_set(x_9, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec_ref(x_22);
lean_free_object(x_9);
lean_free_object(x_3);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
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
uint8_t x_34; 
lean_dec(x_19);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_18, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_3, 3, x_36);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_box(0);
lean_ctor_set(x_3, 3, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_9);
lean_free_object(x_3);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
lean_dec(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_45 = l_Lean_Meta_whnfForall(x_44, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 7)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 2);
lean_inc_ref(x_49);
lean_dec(x_46);
x_50 = l_Lean_Meta_isExprDefEq(x_2, x_48, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_expr_instantiate1(x_49, x_1);
lean_dec_ref(x_49);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_3, 3, x_54);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_49);
lean_free_object(x_3);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_dec(x_46);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
lean_ctor_set(x_3, 3, x_62);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_3);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_66 = x_45;
} else {
 lean_dec_ref(x_45);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_3, 1);
x_70 = lean_ctor_get(x_3, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_3);
x_71 = lean_ctor_get(x_9, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_72 = x_9;
} else {
 lean_dec_ref(x_9);
 x_72 = lean_box(0);
}
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_73 = l_Lean_Meta_whnfForall(x_71, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 7)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_77);
lean_dec(x_74);
x_78 = l_Lean_Meta_isExprDefEq(x_2, x_76, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_expr_instantiate1(x_77, x_1);
lean_dec_ref(x_77);
if (lean_is_scalar(x_72)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_72;
}
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_69);
lean_ctor_set(x_83, 2, x_70);
lean_ctor_set(x_83, 3, x_82);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_77);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_90 = x_73;
} else {
 lean_dec_ref(x_73);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_68);
lean_ctor_set(x_92, 1, x_69);
lean_ctor_set(x_92, 2, x_70);
lean_ctor_set(x_92, 3, x_91);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_94 = lean_ctor_get(x_73, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_73, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_96 = x_73;
} else {
 lean_dec_ref(x_73);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_st_ref_take(x_1, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_11, 2, x_5);
x_17 = lean_st_ref_set(x_1, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Name_num___override(x_8, x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Name_num___override(x_8, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
x_31 = lean_ctor_get(x_11, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_33);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
lean_ctor_set(x_34, 8, x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Name_num___override(x_8, x_9);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_1, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_43, 6);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_43, 7);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_43, 8);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 lean_ctor_release(x_43, 7);
 lean_ctor_release(x_43, 8);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
lean_ctor_set(x_57, 6, x_50);
lean_ctor_set(x_57, 7, x_51);
lean_ctor_set(x_57, 8, x_52);
x_58 = lean_st_ref_set(x_1, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Name_num___override(x_40, x_41);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(x_6, x_7);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_20 = l_Lean_Elab_Term_elabType(x_1, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_21);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg(x_21, x_2, x_14, x_15, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(x_13, x_14, x_15, x_16, x_17, x_18, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_fvar___override(x_26);
x_29 = l_Lean_Syntax_getId(x_3);
x_30 = l_Lean_Elab_Term_kindOfBinderName(x_29);
lean_inc(x_21);
lean_inc_ref(x_4);
x_31 = l_Lean_LocalContext_mkLocalDecl(x_4, x_26, x_29, x_21, x_5, x_30);
x_32 = lean_box(0);
lean_inc_ref(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_box(0);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_28);
x_35 = l_Lean_Elab_Term_addTermInfo_x27(x_6, x_28, x_32, x_33, x_34, x_7, x_13, x_14, x_15, x_16, x_17, x_18, x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_17, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_17, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_17, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_17, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_17, 7);
lean_inc(x_44);
x_45 = lean_ctor_get(x_17, 8);
lean_inc(x_45);
x_46 = lean_ctor_get(x_17, 9);
lean_inc(x_46);
x_47 = lean_ctor_get(x_17, 10);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_17, sizeof(void*)*13);
x_49 = lean_ctor_get(x_17, 11);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_17, sizeof(void*)*13 + 1);
x_51 = lean_ctor_get(x_17, 12);
lean_inc_ref(x_51);
lean_inc_ref(x_28);
x_52 = lean_array_push(x_8, x_28);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set(x_53, 2, x_9);
lean_ctor_set(x_53, 3, x_10);
x_54 = l_Lean_replaceRef(x_3, x_42);
lean_dec(x_42);
x_55 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_38);
lean_ctor_set(x_55, 2, x_39);
lean_ctor_set(x_55, 3, x_40);
lean_ctor_set(x_55, 4, x_41);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_55, 6, x_43);
lean_ctor_set(x_55, 7, x_44);
lean_ctor_set(x_55, 8, x_45);
lean_ctor_set(x_55, 9, x_46);
lean_ctor_set(x_55, 10, x_47);
lean_ctor_set(x_55, 11, x_49);
lean_ctor_set(x_55, 12, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*13, x_48);
lean_ctor_set_uint8(x_55, sizeof(void*)*13 + 1, x_50);
lean_inc(x_18);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_21);
x_56 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_propagateExpectedType___redArg(x_28, x_21, x_53, x_15, x_16, x_55, x_18, x_36);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_60 = l_Lean_Meta_isClass_x3f(x_21, x_15, x_16, x_17, x_18, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 2);
x_66 = lean_ctor_get(x_58, 3);
x_67 = lean_ctor_get(x_58, 1);
lean_dec(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc_ref(x_31);
lean_inc_ref(x_64);
lean_ctor_set(x_58, 1, x_31);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_free_object(x_56);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
x_68 = x_13;
x_69 = x_14;
x_70 = x_15;
x_71 = x_16;
x_72 = x_17;
x_73 = x_18;
x_74 = x_62;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_box(x_30);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_58);
x_80 = lean_ctor_get(x_61, 0);
lean_inc(x_80);
lean_dec(x_61);
lean_ctor_set(x_56, 1, x_28);
lean_ctor_set(x_56, 0, x_80);
x_81 = lean_array_push(x_65, x_56);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_11, x_82);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_64);
lean_ctor_set(x_84, 1, x_31);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_66);
x_85 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_12, x_83, x_84, x_13, x_14, x_15, x_16, x_17, x_18, x_62);
return x_85;
}
else
{
lean_dec(x_79);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_61);
lean_free_object(x_56);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
x_68 = x_13;
x_69 = x_14;
x_70 = x_15;
x_71 = x_16;
x_72 = x_17;
x_73 = x_18;
x_74 = x_62;
goto block_78;
}
}
block_78:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_11, x_75);
x_77 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_12, x_76, x_58, x_68, x_69, x_70, x_71, x_72, x_73, x_74);
return x_77;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = lean_ctor_get(x_58, 0);
x_87 = lean_ctor_get(x_58, 2);
x_88 = lean_ctor_get(x_58, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_58);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc_ref(x_31);
lean_inc_ref(x_86);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_31);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_free_object(x_56);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
x_90 = x_13;
x_91 = x_14;
x_92 = x_15;
x_93 = x_16;
x_94 = x_17;
x_95 = x_18;
x_96 = x_62;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_box(x_30);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_89);
x_102 = lean_ctor_get(x_61, 0);
lean_inc(x_102);
lean_dec(x_61);
lean_ctor_set(x_56, 1, x_28);
lean_ctor_set(x_56, 0, x_102);
x_103 = lean_array_push(x_87, x_56);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_11, x_104);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_86);
lean_ctor_set(x_106, 1, x_31);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_88);
x_107 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_12, x_105, x_106, x_13, x_14, x_15, x_16, x_17, x_18, x_62);
return x_107;
}
else
{
lean_dec(x_101);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec(x_61);
lean_free_object(x_56);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
x_90 = x_13;
x_91 = x_14;
x_92 = x_15;
x_93 = x_16;
x_94 = x_17;
x_95 = x_18;
x_96 = x_62;
goto block_100;
}
}
block_100:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_11, x_97);
x_99 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_12, x_98, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
return x_99;
}
}
}
else
{
uint8_t x_108; 
lean_free_object(x_56);
lean_dec(x_58);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_108 = !lean_is_exclusive(x_60);
if (x_108 == 0)
{
return x_60;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_60, 0);
x_110 = lean_ctor_get(x_60, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_60);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_56, 0);
x_113 = lean_ctor_get(x_56, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_56);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_114 = l_Lean_Meta_isClass_x3f(x_21, x_15, x_16, x_17, x_18, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_112, 2);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_112, 3);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
lean_inc(x_119);
lean_inc_ref(x_118);
lean_inc_ref(x_31);
lean_inc_ref(x_117);
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 4, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_31);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_119);
if (lean_obj_tag(x_115) == 0)
{
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
x_122 = x_13;
x_123 = x_14;
x_124 = x_15;
x_125 = x_16;
x_126 = x_17;
x_127 = x_18;
x_128 = x_116;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_box(x_30);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_121);
x_134 = lean_ctor_get(x_115, 0);
lean_inc(x_134);
lean_dec(x_115);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_28);
x_136 = lean_array_push(x_118, x_135);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_11, x_137);
x_139 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_139, 0, x_117);
lean_ctor_set(x_139, 1, x_31);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_119);
x_140 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_12, x_138, x_139, x_13, x_14, x_15, x_16, x_17, x_18, x_116);
return x_140;
}
else
{
lean_dec(x_133);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_115);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
x_122 = x_13;
x_123 = x_14;
x_124 = x_15;
x_125 = x_16;
x_126 = x_17;
x_127 = x_18;
x_128 = x_116;
goto block_132;
}
}
block_132:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_add(x_11, x_129);
x_131 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_12, x_130, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_112);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_141 = lean_ctor_get(x_114, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_114, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_143 = x_114;
} else {
 lean_dec_ref(x_114);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
return x_56;
}
}
else
{
uint8_t x_145; 
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
x_145 = !lean_is_exclusive(x_35);
if (x_145 == 0)
{
return x_35;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_35, 0);
x_147 = lean_ctor_get(x_35, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_35);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_149 = !lean_is_exclusive(x_20);
if (x_149 == 0)
{
return x_20;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_20, 0);
x_151 = lean_ctor_get(x_20, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_20);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_21 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
lean_dec_ref(x_3);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_8, 5);
x_27 = lean_box(x_20);
x_28 = lean_box(x_12);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc(x_19);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed), 19, 12);
lean_closure_set(x_29, 0, x_19);
lean_closure_set(x_29, 1, x_14);
lean_closure_set(x_29, 2, x_18);
lean_closure_set(x_29, 3, x_22);
lean_closure_set(x_29, 4, x_27);
lean_closure_set(x_29, 5, x_17);
lean_closure_set(x_29, 6, x_28);
lean_closure_set(x_29, 7, x_21);
lean_closure_set(x_29, 8, x_23);
lean_closure_set(x_29, 9, x_24);
lean_closure_set(x_29, 10, x_2);
lean_closure_set(x_29, 11, x_1);
x_30 = l_Lean_replaceRef(x_19, x_26);
lean_dec(x_26);
lean_dec(x_19);
lean_ctor_set(x_8, 5, x_30);
x_31 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_22, x_23, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
x_34 = lean_ctor_get(x_8, 2);
x_35 = lean_ctor_get(x_8, 3);
x_36 = lean_ctor_get(x_8, 4);
x_37 = lean_ctor_get(x_8, 5);
x_38 = lean_ctor_get(x_8, 6);
x_39 = lean_ctor_get(x_8, 7);
x_40 = lean_ctor_get(x_8, 8);
x_41 = lean_ctor_get(x_8, 9);
x_42 = lean_ctor_get(x_8, 10);
x_43 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_44 = lean_ctor_get(x_8, 11);
x_45 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_46 = lean_ctor_get(x_8, 12);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_47 = lean_box(x_20);
x_48 = lean_box(x_12);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc(x_19);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed), 19, 12);
lean_closure_set(x_49, 0, x_19);
lean_closure_set(x_49, 1, x_14);
lean_closure_set(x_49, 2, x_18);
lean_closure_set(x_49, 3, x_22);
lean_closure_set(x_49, 4, x_47);
lean_closure_set(x_49, 5, x_17);
lean_closure_set(x_49, 6, x_48);
lean_closure_set(x_49, 7, x_21);
lean_closure_set(x_49, 8, x_23);
lean_closure_set(x_49, 9, x_24);
lean_closure_set(x_49, 10, x_2);
lean_closure_set(x_49, 11, x_1);
x_50 = l_Lean_replaceRef(x_19, x_37);
lean_dec(x_37);
lean_dec(x_19);
x_51 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_33);
lean_ctor_set(x_51, 2, x_34);
lean_ctor_set(x_51, 3, x_35);
lean_ctor_set(x_51, 4, x_36);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_38);
lean_ctor_set(x_51, 7, x_39);
lean_ctor_set(x_51, 8, x_40);
lean_ctor_set(x_51, 9, x_41);
lean_ctor_set(x_51, 10, x_42);
lean_ctor_set(x_51, 11, x_44);
lean_ctor_set(x_51, 12, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*13, x_43);
lean_ctor_set_uint8(x_51, sizeof(void*)*13 + 1, x_45);
x_52 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_22, x_23, x_49, x_4, x_5, x_6, x_7, x_51, x_9, x_16);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_15);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshFVarId___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_5);
x_21 = lean_unbox(x_7);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___lam__0(x_1, x_2, x_3, x_4, x_20, x_6, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_11);
lean_dec(x_3);
return x_22;
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_19;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_FunBinders_elabFunBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFunBinders___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Meta_getLocalInstances___redArg(x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Elab_Term_elabFunBinders___redArg___closed__0;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_19 = l_Lean_Elab_Term_FunBinders_elabFunBindersAux(x_1, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_20, 3);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_apply_2(x_3, x_22, x_25);
x_27 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_23, x_24, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Elab_Term_elabFunBinders___redArg___closed__0;
x_33 = lean_apply_9(x_3, x_32, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabFunBinders___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabFunBinders___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFunBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabFunBinders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_12;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letRecDecl", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___closed__0;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_11 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_10);
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_6, x_5, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_18 = lean_array_uset(x_15, x_5, x_9);
x_5 = x_17;
x_6 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letrec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letRecDecls", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("whereDecls", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__9;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("whereFinally", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__11;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandWhereDecls___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_34; uint8_t x_35; 
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_7 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_34 = l_Lean_Elab_Term_expandWhereDecls___closed__10;
lean_inc(x_1);
x_35 = l_Lean_Syntax_isOfKind(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_55; uint8_t x_56; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Syntax_getArg(x_1, x_38);
lean_inc(x_55);
x_56 = l_Lean_Syntax_matchesNull(x_55, x_37);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l_Lean_Syntax_getArgs(x_55);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_expandWhereDecls___closed__13;
x_59 = lean_array_get_size(x_57);
x_60 = lean_nat_dec_lt(x_37, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec_ref(x_57);
x_39 = x_58;
goto block_54;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec_ref(x_57);
x_39 = x_58;
goto block_54;
}
else
{
lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_box(x_35);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = 0;
x_65 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_66 = l_Array_foldlMUnsafe_fold___at___Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(x_35, x_56, x_57, x_64, x_65, x_63);
lean_dec_ref(x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_39 = x_67;
goto block_54;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_unsigned_to_nat(2u);
x_69 = l_Lean_Syntax_getArg(x_1, x_68);
lean_dec(x_1);
x_70 = l_Lean_Syntax_isNone(x_69);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; 
lean_inc(x_69);
x_71 = l_Lean_Syntax_matchesNull(x_69, x_38);
if (x_71 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = l_Lean_Syntax_getArgs(x_55);
lean_dec(x_55);
x_86 = l_Lean_Elab_Term_expandWhereDecls___closed__13;
x_87 = lean_array_get_size(x_85);
x_88 = lean_nat_dec_lt(x_37, x_87);
if (x_88 == 0)
{
lean_dec(x_87);
lean_dec_ref(x_85);
x_72 = x_86;
goto block_84;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_87, x_87);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec_ref(x_85);
x_72 = x_86;
goto block_84;
}
else
{
lean_object* x_90; lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_box(x_56);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
x_92 = 0;
x_93 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_94 = l_Array_foldlMUnsafe_fold___at___Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(x_56, x_71, x_85, x_92, x_93, x_91);
lean_dec_ref(x_85);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec_ref(x_94);
x_72 = x_95;
goto block_84;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_96 = l_Lean_Syntax_getArg(x_69, x_37);
lean_dec(x_69);
x_97 = l_Lean_Elab_Term_expandWhereDecls___closed__12;
x_98 = l_Lean_Syntax_isOfKind(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = l_Lean_Syntax_getArgs(x_55);
lean_dec(x_55);
x_110 = l_Lean_Elab_Term_expandWhereDecls___closed__13;
x_111 = lean_array_get_size(x_109);
x_112 = lean_nat_dec_lt(x_37, x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec_ref(x_109);
x_99 = x_110;
goto block_108;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_111, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec_ref(x_109);
x_99 = x_110;
goto block_108;
}
else
{
lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_box(x_71);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_110);
x_116 = 0;
x_117 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_118 = l_Array_foldlMUnsafe_fold___at___Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(x_71, x_98, x_109, x_116, x_117, x_115);
lean_dec_ref(x_109);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec_ref(x_118);
x_99 = x_119;
goto block_108;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_55);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_2);
lean_ctor_set(x_120, 1, x_4);
return x_120;
}
block_108:
{
size_t x_100; size_t x_101; lean_object* x_102; 
x_100 = lean_array_size(x_99);
x_101 = 0;
x_102 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(x_5, x_6, x_7, x_100, x_101, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
lean_dec(x_2);
x_103 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_103;
}
else
{
if (x_70 == 0)
{
if (x_71 == 0)
{
lean_object* x_104; 
lean_dec(x_102);
lean_dec(x_2);
x_104 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_104;
}
else
{
if (x_98 == 0)
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_2);
x_105 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_105;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_102, 0);
lean_inc(x_106);
lean_dec(x_102);
x_8 = x_106;
x_9 = x_3;
x_10 = x_4;
goto block_33;
}
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
x_8 = x_107;
x_9 = x_3;
x_10 = x_4;
goto block_33;
}
}
}
}
block_84:
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = lean_array_size(x_72);
x_74 = 0;
x_75 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(x_5, x_6, x_7, x_73, x_74, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_2);
x_76 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_76;
}
else
{
if (x_70 == 0)
{
if (x_71 == 0)
{
lean_object* x_77; 
lean_dec(x_75);
lean_dec(x_69);
lean_dec(x_2);
x_77 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l_Lean_Syntax_getArg(x_69, x_37);
lean_dec(x_69);
x_80 = l_Lean_Elab_Term_expandWhereDecls___closed__12;
x_81 = l_Lean_Syntax_isOfKind(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_2);
x_82 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_82;
}
else
{
x_8 = x_78;
x_9 = x_3;
x_10 = x_4;
goto block_33;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_69);
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
lean_dec(x_75);
x_8 = x_83;
x_9 = x_3;
x_10 = x_4;
goto block_33;
}
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_69);
lean_dec(x_55);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_2);
lean_ctor_set(x_121, 1, x_4);
return x_121;
}
}
block_54:
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = lean_array_size(x_39);
x_41 = 0;
x_42 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(x_5, x_6, x_7, x_40, x_41, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(2u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
lean_dec(x_1);
x_47 = l_Lean_Syntax_isNone(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_inc(x_46);
x_48 = l_Lean_Syntax_matchesNull(x_46, x_38);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_2);
x_49 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Syntax_getArg(x_46, x_37);
lean_dec(x_46);
x_51 = l_Lean_Elab_Term_expandWhereDecls___closed__12;
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_44);
lean_dec(x_2);
x_53 = l_Lean_Macro_throwUnsupported___redArg(x_4);
return x_53;
}
else
{
x_8 = x_44;
x_9 = x_3;
x_10 = x_4;
goto block_33;
}
}
}
else
{
lean_dec(x_46);
x_8 = x_44;
x_9 = x_3;
x_10 = x_4;
goto block_33;
}
}
}
}
block_33:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_11 = lean_ctor_get(x_9, 5);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
x_14 = l_Lean_Elab_Term_expandWhereDecls___closed__1;
x_15 = l_Lean_Elab_Term_expandWhereDecls___closed__3;
x_16 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
lean_inc(x_13);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Term_expandWhereDecls___closed__5;
lean_inc(x_13);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_13);
x_20 = l_Lean_Syntax_node2(x_13, x_15, x_17, x_19);
x_21 = l_Lean_Elab_Term_expandWhereDecls___closed__7;
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_23 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_24 = l_Lean_Elab_Term_expandForall___closed__4;
x_25 = l_Lean_Syntax_SepArray_ofElems(x_24, x_8);
lean_dec_ref(x_8);
x_26 = l_Array_append___redArg(x_23, x_25);
lean_dec_ref(x_25);
lean_inc(x_13);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_13);
x_28 = l_Lean_Syntax_node1(x_13, x_21, x_27);
x_29 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_13);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Syntax_node4(x_13, x_14, x_20, x_28, x_30, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_expandWhereDecls(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
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
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_10 = lean_array_uget(x_8, x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_8, x_7, x_11);
x_13 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_13);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Syntax_node2(x_4, x_14, x_5, x_10);
x_16 = 1;
x_17 = lean_usize_add(x_7, x_16);
x_18 = lean_array_uset(x_12, x_7, x_15);
x_7 = x_17;
x_8 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_9 = lean_array_uget(x_7, x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_7, x_6, x_10);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_13 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Name_mkStr4(x_1, x_2, x_12, x_13);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Syntax_node2(x_3, x_14, x_4, x_9);
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
x_18 = lean_array_uset(x_11, x_6, x_15);
x_6 = x_17;
x_7 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandForall___closed__4;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explicit", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fun", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("basicFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__9;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seq1", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__11;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__1;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 1)
{
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_11 = lean_ctor_get(x_7, 5);
lean_inc(x_11);
x_12 = l_Lean_SourceInfo_fromRef(x_11, x_2);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_14 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_16 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_17 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_20 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_12);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_size(x_5);
x_23 = 0;
lean_inc_ref(x_21);
lean_inc(x_12);
x_24 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(x_13, x_14, x_15, x_12, x_21, x_22, x_23, x_5);
x_25 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0;
x_26 = l_Lean_mkSepArray(x_24, x_25);
lean_dec_ref(x_24);
x_27 = l_Array_append___redArg(x_20, x_26);
lean_dec_ref(x_26);
lean_inc(x_12);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_12);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
lean_inc_ref(x_21);
x_31 = l_Lean_Syntax_node6(x_12, x_17, x_18, x_21, x_21, x_28, x_30, x_1);
x_32 = l_Lean_Elab_Term_clearInMatch(x_31, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_6);
x_33 = lean_ctor_get(x_7, 5);
lean_inc(x_33);
lean_dec_ref(x_7);
x_34 = 0;
x_35 = l_Lean_SourceInfo_fromRef(x_33, x_34);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_37 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_38 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_39 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__2;
lean_inc(x_35);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_42 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_35);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_size(x_5);
x_45 = 0;
lean_inc_ref(x_43);
lean_inc(x_35);
x_46 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(x_36, x_37, x_35, x_43, x_44, x_45, x_5);
x_47 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0;
x_48 = l_Lean_mkSepArray(x_46, x_47);
lean_dec_ref(x_46);
x_49 = l_Array_append___redArg(x_42, x_48);
lean_dec_ref(x_48);
lean_inc(x_35);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_49);
x_51 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_35);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_35);
lean_ctor_set(x_52, 1, x_51);
lean_inc_ref(x_43);
x_53 = l_Lean_Syntax_node6(x_35, x_39, x_40, x_43, x_43, x_50, x_52, x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_8);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_7);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_7, 1);
x_59 = lean_ctor_get(x_7, 5);
x_60 = lean_ctor_get(x_7, 2);
lean_dec(x_60);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_57, x_61);
lean_ctor_set(x_8, 0, x_62);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_58);
lean_ctor_set(x_7, 2, x_57);
x_63 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_8);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_nat_sub(x_4, x_61);
x_72 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_73 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_74 = l_Lean_addMacroScope(x_58, x_73, x_57);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_75);
x_77 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_78 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_69);
lean_ctor_set_tag(x_67, 2);
lean_ctor_set(x_67, 1, x_78);
lean_inc_ref(x_76);
x_79 = l_Lean_Syntax_node2(x_69, x_77, x_67, x_76);
x_80 = lean_array_push(x_5, x_79);
lean_inc_ref(x_76);
x_81 = lean_array_push(x_6, x_76);
lean_inc_ref(x_7);
x_82 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_71, x_80, x_81, x_7, x_70);
lean_dec(x_71);
if (x_2 == 0)
{
if (x_3 == 0)
{
uint8_t x_83; 
lean_dec_ref(x_7);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = l_Lean_SourceInfo_fromRef(x_59, x_3);
lean_dec(x_59);
x_86 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_87 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_85);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_86);
lean_ctor_set(x_63, 0, x_85);
x_88 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_85);
x_90 = l_Lean_Syntax_node1(x_85, x_89, x_76);
x_91 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_85);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_85);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_93);
lean_inc(x_85);
x_95 = l_Lean_Syntax_node4(x_85, x_88, x_90, x_92, x_94, x_84);
x_96 = l_Lean_Syntax_node2(x_85, x_87, x_63, x_95);
lean_ctor_set(x_82, 0, x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_82, 0);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_82);
x_99 = l_Lean_SourceInfo_fromRef(x_59, x_3);
lean_dec(x_59);
x_100 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_101 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_99);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_100);
lean_ctor_set(x_63, 0, x_99);
x_102 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_103 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_99);
x_104 = l_Lean_Syntax_node1(x_99, x_103, x_76);
x_105 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_99);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_103);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_99);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_99);
x_109 = l_Lean_Syntax_node4(x_99, x_102, x_104, x_106, x_108, x_97);
x_110 = l_Lean_Syntax_node2(x_99, x_101, x_63, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_98);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_82, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_82, 1);
lean_inc(x_113);
lean_dec_ref(x_82);
x_114 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_113);
lean_dec_ref(x_7);
lean_dec(x_59);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_78);
lean_ctor_set(x_63, 0, x_116);
x_117 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_118 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_116);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
x_120 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_121 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_116);
x_122 = l_Lean_Syntax_node1(x_116, x_121, x_76);
x_123 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_116);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_116);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_123);
x_125 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_116);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_116);
x_127 = l_Lean_Syntax_node4(x_116, x_120, x_122, x_124, x_126, x_112);
lean_inc(x_116);
x_128 = l_Lean_Syntax_node2(x_116, x_118, x_119, x_127);
x_129 = l_Lean_Syntax_node2(x_116, x_77, x_63, x_128);
lean_ctor_set(x_114, 0, x_129);
return x_114;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_130 = lean_ctor_get(x_114, 0);
x_131 = lean_ctor_get(x_114, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_114);
lean_inc(x_130);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_78);
lean_ctor_set(x_63, 0, x_130);
x_132 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_133 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_130);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_132);
x_135 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_136 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_130);
x_137 = l_Lean_Syntax_node1(x_130, x_136, x_76);
x_138 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_130);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_136);
lean_ctor_set(x_139, 2, x_138);
x_140 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_130);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_130);
lean_ctor_set(x_141, 1, x_140);
lean_inc(x_130);
x_142 = l_Lean_Syntax_node4(x_130, x_135, x_137, x_139, x_141, x_112);
lean_inc(x_130);
x_143 = l_Lean_Syntax_node2(x_130, x_133, x_134, x_142);
x_144 = l_Lean_Syntax_node2(x_130, x_77, x_63, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_131);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_82, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_82, 1);
lean_inc(x_147);
lean_dec_ref(x_82);
x_148 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_147);
lean_dec_ref(x_7);
lean_dec(x_59);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_152 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_153 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_154 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_150);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_153);
lean_ctor_set(x_63, 0, x_150);
lean_inc(x_150);
x_155 = l_Lean_Syntax_node1(x_150, x_152, x_76);
lean_inc(x_150);
x_156 = l_Lean_Syntax_node2(x_150, x_154, x_63, x_155);
x_157 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_150);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_157);
lean_inc(x_150);
x_159 = l_Lean_Syntax_node3(x_150, x_152, x_156, x_158, x_146);
x_160 = l_Lean_Syntax_node1(x_150, x_151, x_159);
lean_ctor_set(x_148, 0, x_160);
return x_148;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_161 = lean_ctor_get(x_148, 0);
x_162 = lean_ctor_get(x_148, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_148);
x_163 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_164 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_165 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_166 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_161);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_165);
lean_ctor_set(x_63, 0, x_161);
lean_inc(x_161);
x_167 = l_Lean_Syntax_node1(x_161, x_164, x_76);
lean_inc(x_161);
x_168 = l_Lean_Syntax_node2(x_161, x_166, x_63, x_167);
x_169 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_161);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_161);
x_171 = l_Lean_Syntax_node3(x_161, x_164, x_168, x_170, x_146);
x_172 = l_Lean_Syntax_node1(x_161, x_163, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_162);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_174 = lean_ctor_get(x_67, 0);
x_175 = lean_ctor_get(x_67, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_67);
x_176 = lean_nat_sub(x_4, x_61);
x_177 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_178 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_179 = l_Lean_addMacroScope(x_58, x_178, x_57);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_181, 0, x_65);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
x_182 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_183 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_174);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_174);
lean_ctor_set(x_184, 1, x_183);
lean_inc_ref(x_181);
x_185 = l_Lean_Syntax_node2(x_174, x_182, x_184, x_181);
x_186 = lean_array_push(x_5, x_185);
lean_inc_ref(x_181);
x_187 = lean_array_push(x_6, x_181);
lean_inc_ref(x_7);
x_188 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_176, x_186, x_187, x_7, x_175);
lean_dec(x_176);
if (x_2 == 0)
{
if (x_3 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec_ref(x_7);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = l_Lean_SourceInfo_fromRef(x_59, x_3);
lean_dec(x_59);
x_193 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_194 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_192);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_193);
lean_ctor_set(x_63, 0, x_192);
x_195 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_196 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_192);
x_197 = l_Lean_Syntax_node1(x_192, x_196, x_181);
x_198 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_192);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_192);
lean_ctor_set(x_199, 1, x_196);
lean_ctor_set(x_199, 2, x_198);
x_200 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_192);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_192);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_192);
x_202 = l_Lean_Syntax_node4(x_192, x_195, x_197, x_199, x_201, x_189);
x_203 = l_Lean_Syntax_node2(x_192, x_194, x_63, x_202);
if (lean_is_scalar(x_191)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_191;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_190);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_205 = lean_ctor_get(x_188, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_188, 1);
lean_inc(x_206);
lean_dec_ref(x_188);
x_207 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_206);
lean_dec_ref(x_7);
lean_dec(x_59);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
lean_inc(x_208);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_183);
lean_ctor_set(x_63, 0, x_208);
x_211 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_212 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_208);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_208);
lean_ctor_set(x_213, 1, x_211);
x_214 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_215 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_208);
x_216 = l_Lean_Syntax_node1(x_208, x_215, x_181);
x_217 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_208);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_215);
lean_ctor_set(x_218, 2, x_217);
x_219 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_208);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_208);
lean_ctor_set(x_220, 1, x_219);
lean_inc(x_208);
x_221 = l_Lean_Syntax_node4(x_208, x_214, x_216, x_218, x_220, x_205);
lean_inc(x_208);
x_222 = l_Lean_Syntax_node2(x_208, x_212, x_213, x_221);
x_223 = l_Lean_Syntax_node2(x_208, x_182, x_63, x_222);
if (lean_is_scalar(x_210)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_210;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_209);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_225 = lean_ctor_get(x_188, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_188, 1);
lean_inc(x_226);
lean_dec_ref(x_188);
x_227 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_226);
lean_dec_ref(x_7);
lean_dec(x_59);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_232 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_233 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_234 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_228);
lean_ctor_set_tag(x_63, 2);
lean_ctor_set(x_63, 1, x_233);
lean_ctor_set(x_63, 0, x_228);
lean_inc(x_228);
x_235 = l_Lean_Syntax_node1(x_228, x_232, x_181);
lean_inc(x_228);
x_236 = l_Lean_Syntax_node2(x_228, x_234, x_63, x_235);
x_237 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_228);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_228);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_228);
x_239 = l_Lean_Syntax_node3(x_228, x_232, x_236, x_238, x_225);
x_240 = l_Lean_Syntax_node1(x_228, x_231, x_239);
if (lean_is_scalar(x_230)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_230;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_229);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_242 = lean_ctor_get(x_63, 0);
x_243 = lean_ctor_get(x_63, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_63);
x_244 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_243);
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
x_248 = lean_nat_sub(x_4, x_61);
x_249 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_250 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_251 = l_Lean_addMacroScope(x_58, x_250, x_57);
x_252 = lean_box(0);
x_253 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_253, 0, x_242);
lean_ctor_set(x_253, 1, x_249);
lean_ctor_set(x_253, 2, x_251);
lean_ctor_set(x_253, 3, x_252);
x_254 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_255 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_245);
if (lean_is_scalar(x_247)) {
 x_256 = lean_alloc_ctor(2, 2, 0);
} else {
 x_256 = x_247;
 lean_ctor_set_tag(x_256, 2);
}
lean_ctor_set(x_256, 0, x_245);
lean_ctor_set(x_256, 1, x_255);
lean_inc_ref(x_253);
x_257 = l_Lean_Syntax_node2(x_245, x_254, x_256, x_253);
x_258 = lean_array_push(x_5, x_257);
lean_inc_ref(x_253);
x_259 = lean_array_push(x_6, x_253);
lean_inc_ref(x_7);
x_260 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_248, x_258, x_259, x_7, x_246);
lean_dec(x_248);
if (x_2 == 0)
{
if (x_3 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec_ref(x_7);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
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
x_264 = l_Lean_SourceInfo_fromRef(x_59, x_3);
lean_dec(x_59);
x_265 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_266 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_264);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
x_268 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_269 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_264);
x_270 = l_Lean_Syntax_node1(x_264, x_269, x_253);
x_271 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_264);
x_272 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_272, 0, x_264);
lean_ctor_set(x_272, 1, x_269);
lean_ctor_set(x_272, 2, x_271);
x_273 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_264);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_264);
lean_ctor_set(x_274, 1, x_273);
lean_inc(x_264);
x_275 = l_Lean_Syntax_node4(x_264, x_268, x_270, x_272, x_274, x_261);
x_276 = l_Lean_Syntax_node2(x_264, x_266, x_267, x_275);
if (lean_is_scalar(x_263)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_263;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_262);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_278 = lean_ctor_get(x_260, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_260, 1);
lean_inc(x_279);
lean_dec_ref(x_260);
x_280 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_279);
lean_dec_ref(x_7);
lean_dec(x_59);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
lean_inc(x_281);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_255);
x_285 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_286 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_281);
x_287 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_287, 0, x_281);
lean_ctor_set(x_287, 1, x_285);
x_288 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_289 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_281);
x_290 = l_Lean_Syntax_node1(x_281, x_289, x_253);
x_291 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_281);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_281);
lean_ctor_set(x_292, 1, x_289);
lean_ctor_set(x_292, 2, x_291);
x_293 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_281);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_281);
lean_ctor_set(x_294, 1, x_293);
lean_inc(x_281);
x_295 = l_Lean_Syntax_node4(x_281, x_288, x_290, x_292, x_294, x_278);
lean_inc(x_281);
x_296 = l_Lean_Syntax_node2(x_281, x_286, x_287, x_295);
x_297 = l_Lean_Syntax_node2(x_281, x_254, x_284, x_296);
if (lean_is_scalar(x_283)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_283;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_282);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_299 = lean_ctor_get(x_260, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_260, 1);
lean_inc(x_300);
lean_dec_ref(x_260);
x_301 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_59, x_7, x_300);
lean_dec_ref(x_7);
lean_dec(x_59);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_305 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_306 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_307 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_308 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_302);
x_309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_307);
lean_inc(x_302);
x_310 = l_Lean_Syntax_node1(x_302, x_306, x_253);
lean_inc(x_302);
x_311 = l_Lean_Syntax_node2(x_302, x_308, x_309, x_310);
x_312 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_302);
x_313 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_313, 0, x_302);
lean_ctor_set(x_313, 1, x_312);
lean_inc(x_302);
x_314 = l_Lean_Syntax_node3(x_302, x_306, x_311, x_313, x_299);
x_315 = l_Lean_Syntax_node1(x_302, x_305, x_314);
if (lean_is_scalar(x_304)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_304;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_303);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_317 = lean_ctor_get(x_8, 0);
x_318 = lean_ctor_get(x_7, 0);
x_319 = lean_ctor_get(x_7, 1);
x_320 = lean_ctor_get(x_7, 3);
x_321 = lean_ctor_get(x_7, 4);
x_322 = lean_ctor_get(x_7, 5);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_7);
x_323 = lean_unsigned_to_nat(1u);
x_324 = lean_nat_add(x_317, x_323);
lean_ctor_set(x_8, 0, x_324);
lean_inc(x_322);
lean_inc(x_317);
lean_inc(x_319);
x_325 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_325, 0, x_318);
lean_ctor_set(x_325, 1, x_319);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_320);
lean_ctor_set(x_325, 4, x_321);
lean_ctor_set(x_325, 5, x_322);
x_326 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_322, x_325, x_8);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_329 = x_326;
} else {
 lean_dec_ref(x_326);
 x_329 = lean_box(0);
}
x_330 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_322, x_325, x_328);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = lean_nat_sub(x_4, x_323);
x_335 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_336 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_337 = l_Lean_addMacroScope(x_319, x_336, x_317);
x_338 = lean_box(0);
x_339 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_339, 0, x_327);
lean_ctor_set(x_339, 1, x_335);
lean_ctor_set(x_339, 2, x_337);
lean_ctor_set(x_339, 3, x_338);
x_340 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_341 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_331);
if (lean_is_scalar(x_333)) {
 x_342 = lean_alloc_ctor(2, 2, 0);
} else {
 x_342 = x_333;
 lean_ctor_set_tag(x_342, 2);
}
lean_ctor_set(x_342, 0, x_331);
lean_ctor_set(x_342, 1, x_341);
lean_inc_ref(x_339);
x_343 = l_Lean_Syntax_node2(x_331, x_340, x_342, x_339);
x_344 = lean_array_push(x_5, x_343);
lean_inc_ref(x_339);
x_345 = lean_array_push(x_6, x_339);
lean_inc_ref(x_325);
x_346 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_334, x_344, x_345, x_325, x_332);
lean_dec(x_334);
if (x_2 == 0)
{
if (x_3 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec_ref(x_325);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
x_350 = l_Lean_SourceInfo_fromRef(x_322, x_3);
lean_dec(x_322);
x_351 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_352 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_350);
if (lean_is_scalar(x_329)) {
 x_353 = lean_alloc_ctor(2, 2, 0);
} else {
 x_353 = x_329;
 lean_ctor_set_tag(x_353, 2);
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
x_354 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_355 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_350);
x_356 = l_Lean_Syntax_node1(x_350, x_355, x_339);
x_357 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_350);
x_358 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_358, 0, x_350);
lean_ctor_set(x_358, 1, x_355);
lean_ctor_set(x_358, 2, x_357);
x_359 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_350);
x_360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_360, 0, x_350);
lean_ctor_set(x_360, 1, x_359);
lean_inc(x_350);
x_361 = l_Lean_Syntax_node4(x_350, x_354, x_356, x_358, x_360, x_347);
x_362 = l_Lean_Syntax_node2(x_350, x_352, x_353, x_361);
if (lean_is_scalar(x_349)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_349;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_348);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_364 = lean_ctor_get(x_346, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_346, 1);
lean_inc(x_365);
lean_dec_ref(x_346);
x_366 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_322, x_325, x_365);
lean_dec_ref(x_325);
lean_dec(x_322);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
lean_inc(x_367);
if (lean_is_scalar(x_329)) {
 x_370 = lean_alloc_ctor(2, 2, 0);
} else {
 x_370 = x_329;
 lean_ctor_set_tag(x_370, 2);
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_341);
x_371 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_372 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_367);
x_373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_373, 0, x_367);
lean_ctor_set(x_373, 1, x_371);
x_374 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_375 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_367);
x_376 = l_Lean_Syntax_node1(x_367, x_375, x_339);
x_377 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_367);
x_378 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_378, 0, x_367);
lean_ctor_set(x_378, 1, x_375);
lean_ctor_set(x_378, 2, x_377);
x_379 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_367);
x_380 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_380, 0, x_367);
lean_ctor_set(x_380, 1, x_379);
lean_inc(x_367);
x_381 = l_Lean_Syntax_node4(x_367, x_374, x_376, x_378, x_380, x_364);
lean_inc(x_367);
x_382 = l_Lean_Syntax_node2(x_367, x_372, x_373, x_381);
x_383 = l_Lean_Syntax_node2(x_367, x_340, x_370, x_382);
if (lean_is_scalar(x_369)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_369;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_368);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_385 = lean_ctor_get(x_346, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_346, 1);
lean_inc(x_386);
lean_dec_ref(x_346);
x_387 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_322, x_325, x_386);
lean_dec_ref(x_325);
lean_dec(x_322);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_390 = x_387;
} else {
 lean_dec_ref(x_387);
 x_390 = lean_box(0);
}
x_391 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_392 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_393 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_394 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_388);
if (lean_is_scalar(x_329)) {
 x_395 = lean_alloc_ctor(2, 2, 0);
} else {
 x_395 = x_329;
 lean_ctor_set_tag(x_395, 2);
}
lean_ctor_set(x_395, 0, x_388);
lean_ctor_set(x_395, 1, x_393);
lean_inc(x_388);
x_396 = l_Lean_Syntax_node1(x_388, x_392, x_339);
lean_inc(x_388);
x_397 = l_Lean_Syntax_node2(x_388, x_394, x_395, x_396);
x_398 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_388);
x_399 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_399, 0, x_388);
lean_ctor_set(x_399, 1, x_398);
lean_inc(x_388);
x_400 = l_Lean_Syntax_node3(x_388, x_392, x_397, x_399, x_385);
x_401 = l_Lean_Syntax_node1(x_388, x_391, x_400);
if (lean_is_scalar(x_390)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_390;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_389);
return x_402;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_403 = lean_ctor_get(x_8, 0);
x_404 = lean_ctor_get(x_8, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_8);
x_405 = lean_ctor_get(x_7, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_7, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_7, 3);
lean_inc(x_407);
x_408 = lean_ctor_get(x_7, 4);
lean_inc(x_408);
x_409 = lean_ctor_get(x_7, 5);
lean_inc(x_409);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_410 = x_7;
} else {
 lean_dec_ref(x_7);
 x_410 = lean_box(0);
}
x_411 = lean_unsigned_to_nat(1u);
x_412 = lean_nat_add(x_403, x_411);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_404);
lean_inc(x_409);
lean_inc(x_403);
lean_inc(x_406);
if (lean_is_scalar(x_410)) {
 x_414 = lean_alloc_ctor(0, 6, 0);
} else {
 x_414 = x_410;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_406);
lean_ctor_set(x_414, 2, x_403);
lean_ctor_set(x_414, 3, x_407);
lean_ctor_set(x_414, 4, x_408);
lean_ctor_set(x_414, 5, x_409);
x_415 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_409, x_414, x_413);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_418 = x_415;
} else {
 lean_dec_ref(x_415);
 x_418 = lean_box(0);
}
x_419 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_409, x_414, x_417);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_422 = x_419;
} else {
 lean_dec_ref(x_419);
 x_422 = lean_box(0);
}
x_423 = lean_nat_sub(x_4, x_411);
x_424 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_425 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
x_426 = l_Lean_addMacroScope(x_406, x_425, x_403);
x_427 = lean_box(0);
x_428 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_428, 0, x_416);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_426);
lean_ctor_set(x_428, 3, x_427);
x_429 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_430 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_420);
if (lean_is_scalar(x_422)) {
 x_431 = lean_alloc_ctor(2, 2, 0);
} else {
 x_431 = x_422;
 lean_ctor_set_tag(x_431, 2);
}
lean_ctor_set(x_431, 0, x_420);
lean_ctor_set(x_431, 1, x_430);
lean_inc_ref(x_428);
x_432 = l_Lean_Syntax_node2(x_420, x_429, x_431, x_428);
x_433 = lean_array_push(x_5, x_432);
lean_inc_ref(x_428);
x_434 = lean_array_push(x_6, x_428);
lean_inc_ref(x_414);
x_435 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_2, x_3, x_423, x_433, x_434, x_414, x_421);
lean_dec(x_423);
if (x_2 == 0)
{
if (x_3 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec_ref(x_414);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_438 = x_435;
} else {
 lean_dec_ref(x_435);
 x_438 = lean_box(0);
}
x_439 = l_Lean_SourceInfo_fromRef(x_409, x_3);
lean_dec(x_409);
x_440 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_441 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_439);
if (lean_is_scalar(x_418)) {
 x_442 = lean_alloc_ctor(2, 2, 0);
} else {
 x_442 = x_418;
 lean_ctor_set_tag(x_442, 2);
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
x_443 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_444 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_439);
x_445 = l_Lean_Syntax_node1(x_439, x_444, x_428);
x_446 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_439);
x_447 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_447, 0, x_439);
lean_ctor_set(x_447, 1, x_444);
lean_ctor_set(x_447, 2, x_446);
x_448 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_439);
x_449 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_449, 0, x_439);
lean_ctor_set(x_449, 1, x_448);
lean_inc(x_439);
x_450 = l_Lean_Syntax_node4(x_439, x_443, x_445, x_447, x_449, x_436);
x_451 = l_Lean_Syntax_node2(x_439, x_441, x_442, x_450);
if (lean_is_scalar(x_438)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_438;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_437);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_453 = lean_ctor_get(x_435, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_435, 1);
lean_inc(x_454);
lean_dec_ref(x_435);
x_455 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_409, x_414, x_454);
lean_dec_ref(x_414);
lean_dec(x_409);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_458 = x_455;
} else {
 lean_dec_ref(x_455);
 x_458 = lean_box(0);
}
lean_inc(x_456);
if (lean_is_scalar(x_418)) {
 x_459 = lean_alloc_ctor(2, 2, 0);
} else {
 x_459 = x_418;
 lean_ctor_set_tag(x_459, 2);
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_430);
x_460 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_461 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_456);
x_462 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_462, 0, x_456);
lean_ctor_set(x_462, 1, x_460);
x_463 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_464 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_456);
x_465 = l_Lean_Syntax_node1(x_456, x_464, x_428);
x_466 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_456);
x_467 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_467, 0, x_456);
lean_ctor_set(x_467, 1, x_464);
lean_ctor_set(x_467, 2, x_466);
x_468 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_456);
x_469 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_469, 0, x_456);
lean_ctor_set(x_469, 1, x_468);
lean_inc(x_456);
x_470 = l_Lean_Syntax_node4(x_456, x_463, x_465, x_467, x_469, x_453);
lean_inc(x_456);
x_471 = l_Lean_Syntax_node2(x_456, x_461, x_462, x_470);
x_472 = l_Lean_Syntax_node2(x_456, x_429, x_459, x_471);
if (lean_is_scalar(x_458)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_458;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_457);
return x_473;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_474 = lean_ctor_get(x_435, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_435, 1);
lean_inc(x_475);
lean_dec_ref(x_435);
x_476 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_10, x_409, x_414, x_475);
lean_dec_ref(x_414);
lean_dec(x_409);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_479 = x_476;
} else {
 lean_dec_ref(x_476);
 x_479 = lean_box(0);
}
x_480 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__12;
x_481 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_482 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__13;
x_483 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__14;
lean_inc(x_477);
if (lean_is_scalar(x_418)) {
 x_484 = lean_alloc_ctor(2, 2, 0);
} else {
 x_484 = x_418;
 lean_ctor_set_tag(x_484, 2);
}
lean_ctor_set(x_484, 0, x_477);
lean_ctor_set(x_484, 1, x_482);
lean_inc(x_477);
x_485 = l_Lean_Syntax_node1(x_477, x_481, x_428);
lean_inc(x_477);
x_486 = l_Lean_Syntax_node2(x_477, x_483, x_484, x_485);
x_487 = l_Lean_Elab_Term_expandWhereDecls___closed__8;
lean_inc(x_477);
x_488 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_488, 0, x_477);
lean_ctor_set(x_488, 1, x_487);
lean_inc(x_477);
x_489 = l_Lean_Syntax_node3(x_477, x_481, x_486, x_488, x_474);
x_490 = l_Lean_Syntax_node1(x_477, x_480, x_489);
if (lean_is_scalar(x_479)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_479;
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_478);
return x_491;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___lam__0(x_5, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = 0;
x_9 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_11 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 5, x_11);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_8, x_3, x_9, x_10, x_10, x_4, x_5);
lean_dec(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
x_18 = lean_ctor_get(x_4, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_19 = 0;
x_20 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_21 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_22 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_16);
lean_ctor_set(x_23, 4, x_17);
lean_ctor_set(x_23, 5, x_22);
x_24 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_19, x_3, x_20, x_21, x_21, x_23, x_5);
lean_dec(x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = 1;
x_8 = 0;
x_9 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_11 = l_Lean_replaceRef(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 5, x_11);
x_12 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_7, x_8, x_9, x_10, x_10, x_3, x_4);
lean_dec(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = 1;
x_20 = 0;
x_21 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_2);
x_22 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_16);
lean_ctor_set(x_24, 4, x_17);
lean_ctor_set(x_24, 5, x_23);
x_25 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux(x_2, x_19, x_20, x_21, x_22, x_22, x_24, x_4);
lean_dec(x_21);
return x_25;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Inconsistent number of patterns in match alternatives: This alternative contains ", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nbut a preceding alternative contains ", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_9, x_8);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_array_uget(x_7, x_9);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_eq(x_27, x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_29 = lean_array_fget(x_2, x_3);
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = lean_array_to_list(x_30);
lean_inc(x_4);
x_32 = lean_apply_1(x_4, x_31);
x_33 = lean_array_to_list(x_25);
x_34 = lean_apply_1(x_4, x_33);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1;
x_36 = lean_apply_1(x_5, x_27);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec_ref(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentD(x_34);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Nat_reprFast(x_1);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
x_50 = l_Lean_indentD(x_32);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_26, x_53, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_26);
return x_54;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
x_16 = x_6;
x_17 = x_15;
goto block_21;
}
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_9, x_18);
x_9 = x_19;
x_10 = x_16;
x_15 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_9, x_8);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_array_uget(x_7, x_9);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_eq(x_27, x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_29 = lean_array_fget(x_2, x_3);
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = lean_array_to_list(x_30);
lean_inc(x_4);
x_32 = lean_apply_1(x_4, x_31);
x_33 = lean_array_to_list(x_25);
x_34 = lean_apply_1(x_4, x_33);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1;
x_36 = lean_apply_1(x_5, x_27);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec_ref(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentD(x_34);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Nat_reprFast(x_1);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
x_50 = l_Lean_indentD(x_32);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_26, x_53, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_26);
return x_54;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
x_16 = x_6;
x_17 = x_15;
goto block_21;
}
}
block_21:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_9, x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_16, x_11, x_12, x_13, x_14, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_getAppFn(x_2);
x_9 = l_Lean_Expr_isMVar(x_8);
lean_dec_ref(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_____private_Lean_Meta_Match_Match_0__Lean_Meta_Match_mkIncorrectNumberOfPatternsMsg___at___Lean_Meta_Match_throwIncorrectNumberOfPatternsAt___at_____private_Lean_Elab_Match_0__Lean_Elab_Term_elabPatterns_spec__2_spec__2_spec__2(x_1, x_2);
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__2;
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("patterns", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pattern", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_2 = l_Nat_reprFast(x_1);
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__0;
x_4 = lean_string_append(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_1, x_5);
lean_dec(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__1;
x_8 = lean_string_append(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__2;
x_10 = lean_string_append(x_4, x_9);
return x_10;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Too many patterns in match alternative: At most ", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" expected in a definition of type ", 34, 34);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nbut found ", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot define a value of type", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nby pattern matching because it is not a function type", 54, 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__0___boxed), 7, 0);
x_10 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_11 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = l_Array_filterMapM___at___Lean_Elab_Term_getMatchAlts_spec__0(x_17, x_15, x_18);
lean_dec(x_18);
lean_dec_ref(x_17);
x_20 = lean_array_get_size(x_19);
x_21 = lean_nat_dec_lt(x_15, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_11);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1), 1, 0);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2), 1, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_dec_ref(x_3);
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_14;
goto block_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_nat_dec_lt(x_40, x_2);
if (x_41 == 0)
{
lean_free_object(x_13);
lean_dec(x_40);
lean_dec_ref(x_3);
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_14;
goto block_38;
}
else
{
uint8_t x_42; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
x_42 = lean_nat_dec_eq(x_40, x_15);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_43 = lean_array_fget(x_19, x_15);
lean_dec_ref(x_19);
x_44 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_43, 2);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1;
x_47 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2(x_40);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec_ref(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_indentExpr(x_3);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Nat_reprFast(x_2);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_56);
x_57 = l_Lean_MessageData_ofFormat(x_13);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_to_list(x_44);
x_62 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1(x_61);
x_63 = l_Lean_indentD(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_45, x_66, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_45);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_13);
lean_dec(x_40);
lean_dec(x_2);
x_68 = lean_array_fget(x_19, x_15);
lean_dec_ref(x_19);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7;
x_71 = l_Lean_indentExpr(x_3);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_69, x_74, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_69);
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_13, 0);
lean_inc(x_76);
lean_dec(x_13);
x_77 = lean_nat_dec_lt(x_76, x_2);
if (x_77 == 0)
{
lean_dec(x_76);
lean_dec_ref(x_3);
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_14;
goto block_38;
}
else
{
uint8_t x_78; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
x_78 = lean_nat_dec_eq(x_76, x_15);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_79 = lean_array_fget(x_19, x_15);
lean_dec_ref(x_19);
x_80 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_79, 2);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1;
x_83 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2(x_76);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec_ref(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_indentExpr(x_3);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Nat_reprFast(x_2);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_to_list(x_80);
x_99 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1(x_98);
x_100 = l_Lean_indentD(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_81, x_103, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_81);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_76);
lean_dec(x_2);
x_105 = lean_array_fget(x_19, x_15);
lean_dec_ref(x_19);
x_106 = lean_ctor_get(x_105, 2);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7;
x_108 = l_Lean_indentExpr(x_3);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_106, x_111, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_106);
return x_112;
}
}
}
}
block_38:
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_30 = lean_box(0);
x_31 = lean_array_size(x_19);
x_32 = 0;
x_33 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0(x_2, x_19, x_15, x_23, x_24, x_30, x_19, x_31, x_32, x_30, x_25, x_26, x_27, x_28, x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_19);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_30);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
return x_33;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_ctor_get(x_11, 0);
x_114 = lean_ctor_get(x_11, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_11);
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Lean_Syntax_getArg(x_1, x_115);
x_117 = l_Lean_Syntax_getArgs(x_116);
lean_dec(x_116);
x_118 = lean_array_get_size(x_117);
x_119 = l_Array_filterMapM___at___Lean_Elab_Term_getMatchAlts_spec__0(x_117, x_115, x_118);
lean_dec(x_118);
lean_dec_ref(x_117);
x_120 = lean_array_get_size(x_119);
x_121 = lean_nat_dec_lt(x_115, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_119);
lean_dec(x_113);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_114);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1), 1, 0);
x_125 = lean_alloc_closure((void*)(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2), 1, 0);
if (lean_obj_tag(x_113) == 0)
{
lean_dec_ref(x_3);
x_126 = x_4;
x_127 = x_5;
x_128 = x_6;
x_129 = x_7;
x_130 = x_114;
goto block_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_113, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_140 = x_113;
} else {
 lean_dec_ref(x_113);
 x_140 = lean_box(0);
}
x_141 = lean_nat_dec_lt(x_139, x_2);
if (x_141 == 0)
{
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_3);
x_126 = x_4;
x_127 = x_5;
x_128 = x_6;
x_129 = x_7;
x_130 = x_114;
goto block_138;
}
else
{
uint8_t x_142; 
lean_dec_ref(x_125);
lean_dec_ref(x_124);
x_142 = lean_nat_dec_eq(x_139, x_115);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_143 = lean_array_fget(x_119, x_115);
lean_dec_ref(x_119);
x_144 = lean_ctor_get(x_143, 1);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_143, 2);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1;
x_147 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2(x_139);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec_ref(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
x_150 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3;
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_indentExpr(x_3);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Nat_reprFast(x_2);
if (lean_is_scalar(x_140)) {
 x_157 = lean_alloc_ctor(3, 1, 0);
} else {
 x_157 = x_140;
 lean_ctor_set_tag(x_157, 3);
}
lean_ctor_set(x_157, 0, x_156);
x_158 = l_Lean_MessageData_ofFormat(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_array_to_list(x_144);
x_163 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1(x_162);
x_164 = l_Lean_indentD(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
x_166 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_145, x_167, x_4, x_5, x_6, x_7, x_114);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_145);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_2);
x_169 = lean_array_fget(x_119, x_115);
lean_dec_ref(x_119);
x_170 = lean_ctor_get(x_169, 2);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7;
x_172 = l_Lean_indentExpr(x_3);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9;
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_170, x_175, x_4, x_5, x_6, x_7, x_114);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_170);
return x_176;
}
}
}
block_138:
{
lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; 
x_131 = lean_box(0);
x_132 = lean_array_size(x_119);
x_133 = 0;
x_134 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0(x_2, x_119, x_115, x_124, x_125, x_131, x_119, x_132, x_133, x_131, x_126, x_127, x_128, x_129, x_130);
lean_dec(x_129);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_119);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
return x_134;
}
}
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_11);
if (x_177 == 0)
{
return x_11;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_11, 0);
x_179 = lean_ctor_get(x_11, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_11);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_10 = lean_array_uget(x_8, x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_8, x_7, x_11);
x_13 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_13);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__4;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_15);
x_17 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_4);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_4);
x_19 = l_Lean_Syntax_node2(x_4, x_16, x_18, x_10);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Syntax_node2(x_4, x_14, x_5, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_23 = lean_array_uset(x_12, x_7, x_20);
x_7 = x_22;
x_8 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Elab_Term_clearInMatch(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_Syntax_isNone(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
x_10 = l_Lean_Elab_Term_expandWhereDeclsOpt(x_3, x_7, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_11, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 10);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_20);
lean_dec(x_16);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_1);
lean_dec(x_18);
x_22 = l_Lean_Environment_mainModule(x_20);
lean_dec_ref(x_20);
x_23 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_24 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
lean_inc(x_19);
x_25 = l_Lean_addMacroScope(x_22, x_24, x_19);
x_26 = lean_box(0);
lean_inc(x_21);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_array_push(x_2, x_27);
lean_inc(x_12);
x_29 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_3, x_4, x_5, x_6, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_st_ref_get(x_12, x_32);
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_36);
lean_dec(x_35);
x_37 = l_Lean_Environment_mainModule(x_36);
lean_dec_ref(x_36);
x_38 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_39 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_21);
lean_ctor_set_tag(x_29, 2);
lean_ctor_set(x_29, 1, x_39);
lean_ctor_set(x_29, 0, x_21);
x_40 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_41 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_21);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_40);
lean_ctor_set(x_14, 0, x_21);
x_42 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_44 = l_Lean_addMacroScope(x_37, x_24, x_19);
lean_inc(x_21);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_23);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_26);
lean_inc(x_21);
x_46 = l_Lean_Syntax_node1(x_21, x_43, x_45);
x_47 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_21);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_21);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_21);
x_51 = l_Lean_Syntax_node4(x_21, x_42, x_46, x_48, x_50, x_31);
lean_inc(x_21);
x_52 = l_Lean_Syntax_node2(x_21, x_41, x_14, x_51);
x_53 = l_Lean_Syntax_node2(x_21, x_38, x_29, x_52);
lean_ctor_set(x_33, 0, x_53);
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_56);
lean_dec(x_54);
x_57 = l_Lean_Environment_mainModule(x_56);
lean_dec_ref(x_56);
x_58 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_59 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_21);
lean_ctor_set_tag(x_29, 2);
lean_ctor_set(x_29, 1, x_59);
lean_ctor_set(x_29, 0, x_21);
x_60 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_61 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_21);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_60);
lean_ctor_set(x_14, 0, x_21);
x_62 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_63 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_64 = l_Lean_addMacroScope(x_57, x_24, x_19);
lean_inc(x_21);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_23);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_26);
lean_inc(x_21);
x_66 = l_Lean_Syntax_node1(x_21, x_63, x_65);
x_67 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_21);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_21);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_67);
x_69 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_21);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_69);
lean_inc(x_21);
x_71 = l_Lean_Syntax_node4(x_21, x_62, x_66, x_68, x_70, x_31);
lean_inc(x_21);
x_72 = l_Lean_Syntax_node2(x_21, x_61, x_14, x_71);
x_73 = l_Lean_Syntax_node2(x_21, x_58, x_29, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_55);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_75 = lean_ctor_get(x_29, 0);
x_76 = lean_ctor_get(x_29, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_29);
x_77 = lean_st_ref_get(x_12, x_76);
lean_dec(x_12);
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
x_81 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_81);
lean_dec(x_78);
x_82 = l_Lean_Environment_mainModule(x_81);
lean_dec_ref(x_81);
x_83 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_84 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_21);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_21);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_87 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_21);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_86);
lean_ctor_set(x_14, 0, x_21);
x_88 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_90 = l_Lean_addMacroScope(x_82, x_24, x_19);
lean_inc(x_21);
x_91 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_91, 0, x_21);
lean_ctor_set(x_91, 1, x_23);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_26);
lean_inc(x_21);
x_92 = l_Lean_Syntax_node1(x_21, x_89, x_91);
x_93 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_21);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_21);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_93);
x_95 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_21);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_21);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_21);
x_97 = l_Lean_Syntax_node4(x_21, x_88, x_92, x_94, x_96, x_75);
lean_inc(x_21);
x_98 = l_Lean_Syntax_node2(x_21, x_87, x_14, x_97);
x_99 = l_Lean_Syntax_node2(x_21, x_83, x_85, x_98);
if (lean_is_scalar(x_80)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_80;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_79);
return x_100;
}
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_free_object(x_14);
lean_dec(x_12);
return x_29;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_101 = lean_ctor_get(x_14, 0);
x_102 = lean_ctor_get(x_14, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_14);
x_103 = lean_ctor_get(x_11, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_11, 10);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_105);
lean_dec(x_101);
x_106 = l_Lean_SourceInfo_fromRef(x_103, x_1);
lean_dec(x_103);
x_107 = l_Lean_Environment_mainModule(x_105);
lean_dec_ref(x_105);
x_108 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__3;
x_109 = l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1;
lean_inc(x_104);
x_110 = l_Lean_addMacroScope(x_107, x_109, x_104);
x_111 = lean_box(0);
lean_inc(x_106);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_111);
x_113 = lean_array_push(x_2, x_112);
lean_inc(x_12);
x_114 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_3, x_4, x_5, x_6, x_113, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_st_ref_get(x_12, x_116);
lean_dec(x_12);
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
x_122 = lean_ctor_get(x_119, 0);
lean_inc_ref(x_122);
lean_dec(x_119);
x_123 = l_Lean_Environment_mainModule(x_122);
lean_dec_ref(x_122);
x_124 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_125 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__6;
lean_inc(x_106);
if (lean_is_scalar(x_117)) {
 x_126 = lean_alloc_ctor(2, 2, 0);
} else {
 x_126 = x_117;
 lean_ctor_set_tag(x_126, 2);
}
lean_ctor_set(x_126, 0, x_106);
lean_ctor_set(x_126, 1, x_125);
x_127 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_128 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_106);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_106);
lean_ctor_set(x_129, 1, x_127);
x_130 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
x_131 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_132 = l_Lean_addMacroScope(x_123, x_109, x_104);
lean_inc(x_106);
x_133 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_133, 0, x_106);
lean_ctor_set(x_133, 1, x_108);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_111);
lean_inc(x_106);
x_134 = l_Lean_Syntax_node1(x_106, x_131, x_133);
x_135 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_106);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_106);
lean_ctor_set(x_136, 1, x_131);
lean_ctor_set(x_136, 2, x_135);
x_137 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_106);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_106);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_106);
x_139 = l_Lean_Syntax_node4(x_106, x_130, x_134, x_136, x_138, x_115);
lean_inc(x_106);
x_140 = l_Lean_Syntax_node2(x_106, x_128, x_129, x_139);
x_141 = l_Lean_Syntax_node2(x_106, x_124, x_126, x_140);
if (lean_is_scalar(x_121)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_121;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_120);
return x_142;
}
else
{
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_12);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 1)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_get_size(x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts(x_2, x_15, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_st_ref_get(x_11, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 5);
lean_inc(x_22);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_26 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_27 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_28 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_29 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_24);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_24);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_31 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_24);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_array_size(x_5);
x_34 = 0;
lean_inc_ref(x_5);
lean_inc_ref(x_32);
lean_inc(x_24);
x_35 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(x_25, x_26, x_27, x_24, x_32, x_33, x_34, x_5);
x_36 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0;
x_37 = l_Lean_mkSepArray(x_35, x_36);
lean_dec_ref(x_35);
x_38 = l_Array_append___redArg(x_31, x_37);
lean_dec_ref(x_37);
lean_inc(x_24);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_24);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_40);
lean_inc_ref(x_32);
x_42 = l_Lean_Syntax_node6(x_24, x_29, x_18, x_32, x_32, x_39, x_41, x_2);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0___boxed), 5, 3);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_5);
lean_closure_set(x_43, 2, x_3);
x_44 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_dec(x_18);
x_46 = lean_ctor_get(x_10, 5);
lean_inc(x_46);
x_47 = 0;
x_48 = l_Lean_SourceInfo_fromRef(x_46, x_47);
lean_dec(x_46);
x_49 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_50 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_51 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_52 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
x_53 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1;
lean_inc(x_48);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_56 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_48);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_array_size(x_5);
x_59 = 0;
lean_inc_ref(x_5);
lean_inc_ref(x_57);
lean_inc(x_48);
x_60 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(x_49, x_50, x_51, x_48, x_57, x_58, x_59, x_5);
x_61 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0;
x_62 = l_Lean_mkSepArray(x_60, x_61);
lean_dec_ref(x_60);
x_63 = l_Array_append___redArg(x_56, x_62);
lean_dec_ref(x_62);
lean_inc(x_48);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_48);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_65);
lean_inc_ref(x_57);
x_67 = l_Lean_Syntax_node6(x_48, x_53, x_54, x_57, x_57, x_64, x_66, x_2);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0___boxed), 5, 3);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_5);
lean_closure_set(x_68, 2, x_3);
x_69 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_68, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
return x_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_16, 0);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_16);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_4, x_74);
x_76 = lean_box(x_14);
x_77 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__1___boxed), 13, 10);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_5);
lean_closure_set(x_77, 2, x_1);
lean_closure_set(x_77, 3, x_2);
lean_closure_set(x_77, 4, x_3);
lean_closure_set(x_77, 5, x_75);
lean_closure_set(x_77, 6, x_6);
lean_closure_set(x_77, 7, x_7);
lean_closure_set(x_77, 8, x_8);
lean_closure_set(x_77, 9, x_9);
x_78 = l_Lean_Core_withFreshMacroScope___redArg(x_77, x_10, x_11, x_12);
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAltsWhereDecls_loop_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
x_15 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___lam__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_11);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_16 = l_Lean_Elab_Term_expandMatchAltsWhereDecls_loop(x_2, x_11, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAltsWhereDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_expandMatchAltsWhereDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__7;
x_5 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
lean_inc(x_9);
x_13 = l_Lean_Syntax_isOfKind(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_9, x_11, x_2, x_3);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
x_18 = l_Lean_Syntax_getArg(x_9, x_8);
lean_inc(x_18);
x_19 = l_Lean_Syntax_matchesNull(x_18, x_8);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Syntax_matchesNull(x_18, x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_2);
x_21 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_9, x_22);
lean_dec(x_9);
x_24 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
lean_inc_ref(x_2);
x_25 = l_Lean_Elab_Term_expandFunBinders(x_24, x_23, x_2, x_3);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_2);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec_ref(x_25);
x_31 = l_Lean_Macro_throwUnsupported___redArg(x_30);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_2, 5);
lean_inc(x_40);
lean_dec_ref(x_2);
x_41 = l_Lean_SourceInfo_fromRef(x_40, x_19);
lean_dec(x_40);
lean_inc(x_41);
lean_ctor_set_tag(x_27, 2);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 0, x_41);
x_42 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_43 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_44 = l_Array_append___redArg(x_43, x_35);
lean_dec(x_35);
lean_inc(x_41);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_41);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
x_47 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_41);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_47);
lean_ctor_set(x_26, 0, x_41);
lean_inc(x_41);
x_48 = l_Lean_Syntax_node4(x_41, x_10, x_45, x_46, x_26, x_38);
x_49 = l_Lean_Syntax_node2(x_41, x_5, x_27, x_48);
lean_ctor_set(x_25, 0, x_49);
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
lean_dec(x_27);
x_51 = lean_ctor_get(x_2, 5);
lean_inc(x_51);
lean_dec_ref(x_2);
x_52 = l_Lean_SourceInfo_fromRef(x_51, x_19);
lean_dec(x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_55 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_56 = l_Array_append___redArg(x_55, x_35);
lean_dec(x_35);
lean_inc(x_52);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_52);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_55);
x_59 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_52);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_59);
lean_ctor_set(x_26, 0, x_52);
lean_inc(x_52);
x_60 = l_Lean_Syntax_node4(x_52, x_10, x_57, x_58, x_26, x_50);
x_61 = l_Lean_Syntax_node2(x_52, x_5, x_53, x_60);
lean_ctor_set(x_25, 0, x_61);
return x_25;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_26, 0);
lean_inc(x_62);
lean_dec(x_26);
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_64 = x_27;
} else {
 lean_dec_ref(x_27);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_2, 5);
lean_inc(x_65);
lean_dec_ref(x_2);
x_66 = l_Lean_SourceInfo_fromRef(x_65, x_19);
lean_dec(x_65);
lean_inc(x_66);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(2, 2, 0);
} else {
 x_67 = x_64;
 lean_ctor_set_tag(x_67, 2);
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_4);
x_68 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_69 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_70 = l_Array_append___redArg(x_69, x_62);
lean_dec(x_62);
lean_inc(x_66);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_66);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_69);
x_73 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_66);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_66);
x_75 = l_Lean_Syntax_node4(x_66, x_10, x_71, x_72, x_74, x_63);
x_76 = l_Lean_Syntax_node2(x_66, x_5, x_67, x_75);
lean_ctor_set(x_25, 0, x_76);
return x_25;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
lean_dec(x_25);
x_78 = lean_ctor_get(x_26, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_79 = x_26;
} else {
 lean_dec_ref(x_26);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_27, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_81 = x_27;
} else {
 lean_dec_ref(x_27);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_2, 5);
lean_inc(x_82);
lean_dec_ref(x_2);
x_83 = l_Lean_SourceInfo_fromRef(x_82, x_19);
lean_dec(x_82);
lean_inc(x_83);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(2, 2, 0);
} else {
 x_84 = x_81;
 lean_ctor_set_tag(x_84, 2);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_4);
x_85 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_86 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_87 = l_Array_append___redArg(x_86, x_78);
lean_dec(x_78);
lean_inc(x_83);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_87);
lean_inc(x_83);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
x_90 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_83);
if (lean_is_scalar(x_79)) {
 x_91 = lean_alloc_ctor(2, 2, 0);
} else {
 x_91 = x_79;
 lean_ctor_set_tag(x_91, 2);
}
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_83);
x_92 = l_Lean_Syntax_node4(x_83, x_10, x_88, x_89, x_91, x_80);
x_93 = l_Lean_Syntax_node2(x_83, x_5, x_84, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_77);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_2);
x_95 = !lean_is_exclusive(x_25);
if (x_95 == 0)
{
return x_25;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_25, 0);
x_97 = lean_ctor_get(x_25, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_25);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = l_Lean_Syntax_getArg(x_18, x_16);
lean_dec(x_18);
x_100 = l_Lean_Elab_Term_expandForall___closed__3;
lean_inc(x_99);
x_101 = l_Lean_Syntax_isOfKind(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_99);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_2);
x_102 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; 
x_103 = l_Lean_Syntax_getArg(x_99, x_8);
lean_dec(x_99);
x_104 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_105 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSimpleBinderWithType), 4, 1);
lean_closure_set(x_105, 0, x_103);
x_106 = lean_array_size(x_104);
x_107 = 0;
lean_inc_ref(x_2);
x_108 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandForall_spec__0(x_105, x_106, x_107, x_104, x_2, x_3);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_2, 5);
lean_inc(x_111);
lean_dec_ref(x_2);
x_112 = lean_unsigned_to_nat(3u);
x_113 = l_Lean_Syntax_getArg(x_9, x_112);
lean_dec(x_9);
x_114 = 0;
x_115 = l_Lean_SourceInfo_fromRef(x_111, x_114);
lean_dec(x_111);
lean_inc(x_115);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_4);
x_117 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_118 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_119 = l_Array_append___redArg(x_118, x_110);
lean_dec(x_110);
lean_inc(x_115);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_117);
lean_ctor_set(x_120, 2, x_119);
lean_inc(x_115);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_117);
lean_ctor_set(x_121, 2, x_118);
x_122 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_115);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_115);
lean_ctor_set(x_123, 1, x_122);
lean_inc(x_115);
x_124 = l_Lean_Syntax_node4(x_115, x_10, x_120, x_121, x_123, x_113);
x_125 = l_Lean_Syntax_node2(x_115, x_5, x_116, x_124);
lean_ctor_set(x_108, 0, x_125);
return x_108;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_126 = lean_ctor_get(x_108, 0);
x_127 = lean_ctor_get(x_108, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_108);
x_128 = lean_ctor_get(x_2, 5);
lean_inc(x_128);
lean_dec_ref(x_2);
x_129 = lean_unsigned_to_nat(3u);
x_130 = l_Lean_Syntax_getArg(x_9, x_129);
lean_dec(x_9);
x_131 = 0;
x_132 = l_Lean_SourceInfo_fromRef(x_128, x_131);
lean_dec(x_128);
lean_inc(x_132);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_4);
x_134 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_135 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
x_136 = l_Array_append___redArg(x_135, x_126);
lean_dec(x_126);
lean_inc(x_132);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_136);
lean_inc(x_132);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_138, 2, x_135);
x_139 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_132);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_132);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_132);
x_141 = l_Lean_Syntax_node4(x_132, x_10, x_137, x_138, x_140, x_130);
x_142 = l_Lean_Syntax_node2(x_132, x_5, x_133, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_127);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_9);
lean_dec_ref(x_2);
x_144 = !lean_is_exclusive(x_108);
if (x_144 == 0)
{
return x_108;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_108, 0);
x_146 = lean_ctor_get(x_108, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_108);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandFun", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
x_4 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFun), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(596u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(607u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(41u);
x_4 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = lean_unsigned_to_nat(596u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = lean_unsigned_to_nat(596u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(45u);
x_4 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1;
x_3 = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_2);
x_11 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Syntax_getArg(x_8, x_7);
x_13 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_2);
x_15 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_8, x_12, x_14, x_2, x_3);
lean_dec(x_8);
return x_16;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandExplicitFun", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__5;
x_4 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandExplicitFun), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(609u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(612u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(609u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = lean_unsigned_to_nat(609u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(50u);
x_4 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1;
x_3 = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_19 = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Syntax_getId(x_16);
lean_dec(x_16);
x_22 = lean_array_push(x_4, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_4 = x_22;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
x_16 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_array_size(x_17);
x_20 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(x_17, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_4 = x_22;
x_12 = x_23;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_21;
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckFun___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_55; uint8_t x_56; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
x_55 = l_Lean_Syntax_getArg(x_14, x_13);
x_56 = l_Lean_Syntax_isNone(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_inc(x_55);
x_57 = l_Lean_Syntax_matchesNull(x_55, x_13);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_58 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Syntax_getArg(x_55, x_18);
lean_dec(x_55);
x_60 = l_Lean_Elab_Term_expandForall___closed__3;
x_61 = l_Lean_Syntax_isOfKind(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_62 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg(x_9);
return x_62;
}
else
{
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
goto block_54;
}
}
}
else
{
lean_dec(x_55);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
goto block_54;
}
block_54:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_14, x_28);
lean_dec(x_14);
x_30 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_inc_ref(x_25);
x_32 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_Quotation_precheck_spec__0___redArg(x_31, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Elab_Term_precheckFun___closed__0;
x_39 = lean_array_size(x_36);
x_40 = 0;
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(x_36, x_39, x_40, x_38, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_35);
lean_dec(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(x_42, x_44, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_43);
lean_dec(x_42);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_37);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
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
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_precheckFun_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckFun", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
x_4 = l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_precheckFun), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_13 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_4, x_2, x_2, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = 0;
x_17 = 1;
x_18 = l_Lean_Meta_mkLambdaFVars(x_3, x_14, x_16, x_2, x_16, x_2, x_17, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_18;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__10;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_14, x_13);
x_20 = l_Lean_Syntax_matchesNull(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Syntax_getArg(x_14, x_18);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_14, x_23);
lean_dec(x_14);
x_25 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_24);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_27 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(x_20);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun___lam__0___boxed), 11, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Term_elabFunBinders___redArg(x_31, x_2, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_31);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Elab_Term_elabFun___lam__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabFun", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__8;
x_4 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabFun), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(626u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(639u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(35u);
x_4 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(626u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(626u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(39u);
x_4 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1;
x_3 = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOptNondep", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_LetConfig_setFrom___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOptUsedOnly", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_LetConfig_setFrom___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOptZeta", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_LetConfig_setFrom___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOptPostponeValue", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_LetConfig_setFrom___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOptGeneralize", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_LetConfig_setFrom___closed__8;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_LetConfig_setFrom(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_LetConfig_setFrom___closed__1;
lean_inc(x_2);
x_5 = l_Lean_Syntax_isOfKind(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Term_LetConfig_setFrom___closed__3;
lean_inc(x_2);
x_7 = l_Lean_Syntax_isOfKind(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_Term_LetConfig_setFrom___closed__5;
lean_inc(x_2);
x_9 = l_Lean_Syntax_isOfKind(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_LetConfig_setFrom___closed__7;
lean_inc(x_2);
x_11 = l_Lean_Syntax_isOfKind(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Term_LetConfig_setFrom___closed__9;
x_13 = l_Lean_Syntax_isOfKind(x_2, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 4, x_3);
return x_1;
}
else
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 2, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 3, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 4, x_3);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 3, x_3);
return x_1;
}
else
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 4);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 3, x_3);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 4, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 2, x_3);
return x_1;
}
else
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 4);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 2, x_3);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 3, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 4, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 1, x_3);
return x_1;
}
else
{
uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 4);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 2, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 3, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 4, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_3);
return x_1;
}
else
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_46 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 4);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 2, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 3, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 4, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_LetConfig_setFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Elab_Term_LetConfig_setFrom(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letPosOpt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letNegOpt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOptEq", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letOpts", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__8;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_uget(x_3, x_5);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__1;
lean_inc(x_19);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__3;
lean_inc(x_19);
x_23 = l_Lean_Syntax_isOfKind(x_19, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__5;
lean_inc(x_19);
x_25 = l_Lean_Syntax_isOfKind(x_19, x_24);
if (x_25 == 0)
{
lean_dec(x_19);
x_11 = x_6;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Syntax_getArg(x_19, x_26);
lean_dec(x_19);
x_28 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2;
lean_inc(x_27);
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__7;
x_31 = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(x_30, x_7, x_8, x_9, x_10);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 0);
lean_dec(x_35);
x_36 = l_Lean_mkIdentFrom(x_27, x_32, x_1);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_6, 0, x_37);
x_11 = x_6;
x_12 = x_33;
goto block_16;
}
else
{
uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_39 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_40 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_41 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
lean_dec(x_6);
x_43 = l_Lean_mkIdentFrom(x_27, x_32, x_1);
lean_dec(x_27);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_38);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 1, x_39);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 2, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 3, x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 4, x_42);
x_11 = x_45;
x_12 = x_33;
goto block_16;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_6);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_6, 0);
lean_dec(x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_27);
lean_ctor_set(x_6, 0, x_48);
x_11 = x_6;
x_12 = x_10;
goto block_16;
}
else
{
uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_51 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_52 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_53 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
lean_dec(x_6);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_27);
x_55 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 1, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 2, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 3, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*1 + 4, x_53);
x_11 = x_55;
x_12 = x_10;
goto block_16;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_unsigned_to_nat(1u);
x_57 = l_Lean_Syntax_getArg(x_19, x_56);
lean_dec(x_19);
x_58 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9;
lean_inc(x_57);
x_59 = l_Lean_Syntax_isOfKind(x_57, x_58);
if (x_59 == 0)
{
lean_dec(x_57);
x_11 = x_6;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Syntax_getArg(x_57, x_2);
lean_dec(x_57);
x_61 = l_Lean_Elab_Term_LetConfig_setFrom(x_6, x_60, x_21);
x_11 = x_61;
x_12 = x_10;
goto block_16;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Syntax_getArg(x_19, x_62);
lean_dec(x_19);
x_64 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9;
lean_inc(x_63);
x_65 = l_Lean_Syntax_isOfKind(x_63, x_64);
if (x_65 == 0)
{
lean_dec(x_63);
x_11 = x_6;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Syntax_getArg(x_63, x_2);
lean_dec(x_63);
x_67 = l_Lean_Elab_Term_LetConfig_setFrom(x_6, x_66, x_1);
x_11 = x_67;
x_12 = x_10;
goto block_16;
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_5, x_13);
x_5 = x_14;
x_6 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkLetConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkLetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_mkLetConfig___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_mkLetConfig___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg(x_11, x_13, x_15, x_16, x_17, x_2, x_5, x_7, x_8, x_9);
lean_dec_ref(x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg(x_11, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0(x_14, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_mkLetConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg___lam__0), 9, 3);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(x_1, x_2, x_3, x_14, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_4, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_1, x_3);
x_24 = lean_array_fget(x_14, x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_25 = l_Lean_Elab_Term_addLocalVarInfo(x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_15, x_27);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_28);
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_free_object(x_4);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
x_36 = lean_array_uget(x_1, x_3);
x_37 = lean_array_fget(x_14, x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_38 = l_Lean_Elab_Term_addLocalVarInfo(x_36, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_15, x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_16);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_3 = x_44;
x_4 = x_42;
x_11 = x_39;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to infer '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' declaration type", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to infer universe levels in '", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("have", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = l_Array_unzip___redArg(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType), 8, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = 2;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_19 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = 1;
if (x_4 == 0)
{
lean_object* x_199; 
x_199 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_23 = x_199;
goto block_198;
}
else
{
lean_object* x_200; 
x_200 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6;
x_23 = x_200;
goto block_198;
}
block_198:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__1;
x_25 = l_Lean_stringToMessageData(x_23);
lean_dec_ref(x_23);
lean_inc_ref(x_25);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_1);
x_29 = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(x_20, x_1, x_28, x_7, x_21);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 0, x_33);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_27);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_20);
x_36 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(x_20, x_1, x_35, x_7, x_8, x_31);
if (x_2 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
lean_inc(x_20);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_20);
x_41 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_42 = l_Lean_Elab_Term_elabTermEnsuringType(x_3, x_40, x_22, x_22, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = 1;
lean_inc(x_15);
x_46 = l_Lean_Meta_mkForallFVars(x_15, x_20, x_2, x_22, x_22, x_45, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Meta_mkLambdaFVars(x_15, x_43, x_2, x_2, x_2, x_22, x_45, x_8, x_9, x_10, x_11, x_48);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
if (lean_is_scalar(x_16)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_16;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
lean_ctor_set(x_36, 1, x_52);
lean_ctor_set(x_36, 0, x_47);
lean_ctor_set(x_49, 0, x_36);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
if (lean_is_scalar(x_16)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_16;
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_14);
lean_ctor_set(x_36, 1, x_55);
lean_ctor_set(x_36, 0, x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_47);
lean_free_object(x_36);
lean_dec(x_16);
lean_dec(x_14);
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
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
lean_dec(x_43);
lean_free_object(x_36);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_61 = !lean_is_exclusive(x_46);
if (x_61 == 0)
{
return x_46;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_46, 0);
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_46);
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
lean_free_object(x_36);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_65 = !lean_is_exclusive(x_42);
if (x_65 == 0)
{
return x_42;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_42, 0);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_42);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
lean_dec(x_36);
lean_inc(x_20);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_71 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_72 = l_Lean_Elab_Term_elabTermEnsuringType(x_3, x_70, x_22, x_22, x_71, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = 1;
lean_inc(x_15);
x_76 = l_Lean_Meta_mkForallFVars(x_15, x_20, x_2, x_22, x_22, x_75, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = l_Lean_Meta_mkLambdaFVars(x_15, x_73, x_2, x_2, x_2, x_22, x_75, x_8, x_9, x_10, x_11, x_78);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
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
if (lean_is_scalar(x_16)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_16;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_14);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_77);
lean_dec(x_16);
lean_dec(x_14);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_73);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_94 = lean_ctor_get(x_72, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_96 = x_72;
} else {
 lean_dec_ref(x_72);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_36);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_36, 1);
x_100 = lean_ctor_get(x_36, 0);
lean_dec(x_100);
x_101 = 0;
x_102 = 1;
x_103 = l_Lean_Meta_mkForallFVars(x_15, x_20, x_101, x_22, x_22, x_102, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
lean_inc(x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_107 = 0;
x_108 = lean_box(0);
x_109 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_106, x_107, x_108, x_8, x_9, x_10, x_11, x_105);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
if (lean_is_scalar(x_16)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_16;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_14);
lean_ctor_set(x_36, 1, x_112);
lean_ctor_set(x_36, 0, x_104);
lean_ctor_set(x_109, 0, x_36);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
if (lean_is_scalar(x_16)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_16;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_14);
lean_ctor_set(x_36, 1, x_115);
lean_ctor_set(x_36, 0, x_104);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_36);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_free_object(x_36);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_117 = !lean_is_exclusive(x_103);
if (x_117 == 0)
{
return x_103;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_103, 0);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_103);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_36, 1);
lean_inc(x_121);
lean_dec(x_36);
x_122 = 0;
x_123 = 1;
x_124 = l_Lean_Meta_mkForallFVars(x_15, x_20, x_122, x_22, x_22, x_123, x_8, x_9, x_10, x_11, x_121);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
lean_inc(x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_125);
x_128 = 0;
x_129 = lean_box(0);
x_130 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_127, x_128, x_129, x_8, x_9, x_10, x_11, x_126);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
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
if (lean_is_scalar(x_16)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_16;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_14);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_133;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_137 = lean_ctor_get(x_124, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_124, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_139 = x_124;
} else {
 lean_dec_ref(x_124);
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
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_29, 1);
lean_inc(x_141);
lean_dec(x_29);
x_142 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_25);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_27);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_inc(x_20);
x_146 = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(x_20, x_1, x_145, x_7, x_8, x_141);
if (x_2 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
lean_inc(x_20);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_20);
x_150 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_151 = l_Lean_Elab_Term_elabTermEnsuringType(x_3, x_149, x_22, x_22, x_150, x_6, x_7, x_8, x_9, x_10, x_11, x_147);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = 1;
lean_inc(x_15);
x_155 = l_Lean_Meta_mkForallFVars(x_15, x_20, x_2, x_22, x_22, x_154, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
x_158 = l_Lean_Meta_mkLambdaFVars(x_15, x_152, x_2, x_2, x_2, x_22, x_154, x_8, x_9, x_10, x_11, x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
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
if (lean_is_scalar(x_16)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_16;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_14);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_148;
}
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_156);
lean_dec(x_148);
lean_dec(x_16);
lean_dec(x_14);
x_165 = lean_ctor_get(x_158, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_158, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_167 = x_158;
} else {
 lean_dec_ref(x_158);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_152);
lean_dec(x_148);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_169 = lean_ctor_get(x_155, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_155, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_171 = x_155;
} else {
 lean_dec_ref(x_155);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_148);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_173 = lean_ctor_get(x_151, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_151, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_175 = x_151;
} else {
 lean_dec_ref(x_151);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; lean_object* x_181; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_177 = lean_ctor_get(x_146, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_178 = x_146;
} else {
 lean_dec_ref(x_146);
 x_178 = lean_box(0);
}
x_179 = 0;
x_180 = 1;
x_181 = l_Lean_Meta_mkForallFVars(x_15, x_20, x_179, x_22, x_22, x_180, x_8, x_9, x_10, x_11, x_177);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
lean_inc(x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_182);
x_185 = 0;
x_186 = lean_box(0);
x_187 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_184, x_185, x_186, x_8, x_9, x_10, x_11, x_183);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_16;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_14);
if (lean_is_scalar(x_178)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_178;
}
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_191);
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_190;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_189);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_178);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_194 = lean_ctor_get(x_181, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_181, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_196 = x_181;
} else {
 lean_dec_ref(x_181);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_19);
if (x_201 == 0)
{
return x_19;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_19, 0);
x_203 = lean_ctor_get(x_19, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_19);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_box(0);
lean_inc(x_7);
x_13 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_2, x_11, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_14, x_7, x_15);
lean_dec(x_7);
return x_16;
}
else
{
lean_dec(x_7);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to elaborate with `+generalize`, expected type is not available", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to elaborate with `+generalize`, generalized expected type is not type correct:", 86, 86);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
if (x_1 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_4);
x_26 = lean_box(0);
x_27 = lean_apply_9(x_2, x_3, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__1;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_dec_ref(x_4);
lean_dec(x_2);
x_29 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
lean_dec(x_3);
x_35 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_34, x_10, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_Lean_Expr_getAppFn(x_36);
x_39 = l_Lean_Expr_isMVar(x_38);
lean_dec_ref(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_4, x_10, x_37);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_45 = l_Lean_Meta_kabstract(x_36, x_42, x_44, x_9, x_10, x_11, x_12, x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_expr_instantiate1(x_47, x_5);
lean_dec(x_47);
if (x_6 == 0)
{
lean_free_object(x_45);
lean_free_object(x_40);
x_14 = x_49;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_48;
goto block_25;
}
else
{
lean_object* x_50; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_49);
x_50 = l_Lean_Meta_isTypeCorrect(x_49, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_2);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec_ref(x_50);
x_54 = l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3;
x_55 = l_Lean_MessageData_ofExpr(x_49);
x_56 = l_Lean_indentD(x_55);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_56);
lean_ctor_set(x_45, 0, x_54);
x_57 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_57);
lean_ctor_set(x_40, 0, x_45);
x_58 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_53);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_free_object(x_45);
lean_free_object(x_40);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_dec_ref(x_50);
x_14 = x_49;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_63;
goto block_25;
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_49);
lean_free_object(x_45);
lean_free_object(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
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
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_70 = lean_expr_instantiate1(x_68, x_5);
lean_dec(x_68);
if (x_6 == 0)
{
lean_free_object(x_40);
x_14 = x_70;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_69;
goto block_25;
}
else
{
lean_object* x_71; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_70);
x_71 = l_Lean_Meta_isTypeCorrect(x_70, x_9, x_10, x_11, x_12, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_2);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec_ref(x_71);
x_75 = l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3;
x_76 = l_Lean_MessageData_ofExpr(x_70);
x_77 = l_Lean_indentD(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_79);
lean_ctor_set(x_40, 0, x_78);
x_80 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_74);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
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
lean_object* x_85; 
lean_free_object(x_40);
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
lean_dec_ref(x_71);
x_14 = x_70;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_85;
goto block_25;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_70);
lean_free_object(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_86 = lean_ctor_get(x_71, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_88 = x_71;
} else {
 lean_dec_ref(x_71);
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
lean_free_object(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_40, 0);
x_91 = lean_ctor_get(x_40, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_40);
x_92 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_93 = l_Lean_Meta_kabstract(x_36, x_90, x_92, x_9, x_10, x_11, x_12, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_expr_instantiate1(x_94, x_5);
lean_dec(x_94);
if (x_6 == 0)
{
lean_dec(x_96);
x_14 = x_97;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_95;
goto block_25;
}
else
{
lean_object* x_98; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_97);
x_98 = l_Lean_Meta_isTypeCorrect(x_97, x_9, x_10, x_11, x_12, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec_ref(x_98);
x_102 = l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3;
x_103 = l_Lean_MessageData_ofExpr(x_97);
x_104 = l_Lean_indentD(x_103);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(7, 2, 0);
} else {
 x_105 = x_96;
 lean_ctor_set_tag(x_105, 7);
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_107, x_7, x_8, x_9, x_10, x_11, x_12, x_101);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
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
lean_object* x_113; 
lean_dec(x_96);
x_113 = lean_ctor_get(x_98, 1);
lean_inc(x_113);
lean_dec_ref(x_98);
x_14 = x_97;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_113;
goto block_25;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_114 = lean_ctor_get(x_98, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_98, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_116 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_93;
}
}
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_36);
lean_dec_ref(x_4);
lean_dec(x_2);
x_118 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
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
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_23 = lean_box(0);
x_24 = lean_apply_9(x_2, x_22, x_23, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_17 = l_Lean_Elab_Term_addLocalVarInfo(x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_19 = lean_apply_7(x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_18);
if (lean_obj_tag(x_19) == 0)
{
if (x_3 == 0)
{
if (x_4 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec_ref(x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0;
x_23 = lean_array_push(x_22, x_5);
x_24 = lean_array_push(x_23, x_9);
x_25 = 1;
x_26 = l_Lean_Meta_mkLetFVars(x_24, x_20, x_6, x_4, x_25, x_12, x_13, x_14, x_15, x_21);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec_ref(x_19);
x_29 = l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0;
x_30 = lean_array_push(x_29, x_5);
x_31 = lean_array_push(x_30, x_9);
x_32 = 1;
x_33 = l_Lean_Meta_mkLambdaFVars(x_31, x_27, x_3, x_7, x_3, x_7, x_32, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc_ref(x_8);
x_36 = l_Lean_Meta_mkEqRefl(x_8, x_12, x_13, x_14, x_15, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = l_Lean_mkAppB(x_34, x_8, x_38);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = l_Lean_mkAppB(x_34, x_8, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_8);
return x_36;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_8);
return x_33;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec_ref(x_19);
x_46 = l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0;
x_47 = lean_array_push(x_46, x_5);
x_48 = lean_array_push(x_47, x_9);
x_49 = l_Lean_Expr_abstractM(x_44, x_48, x_12, x_13, x_14, x_15, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
lean_inc_ref(x_8);
x_52 = l_Lean_Meta_mkEqRefl(x_8, x_12, x_13, x_14, x_15, x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_array_push(x_46, x_8);
x_56 = lean_array_push(x_55, x_54);
x_57 = lean_expr_instantiate_rev(x_50, x_56);
lean_dec_ref(x_56);
lean_dec(x_50);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_array_push(x_46, x_8);
x_61 = lean_array_push(x_60, x_58);
x_62 = lean_expr_instantiate_rev(x_50, x_61);
lean_dec_ref(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
lean_dec(x_50);
lean_dec_ref(x_8);
return x_52;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_8);
return x_49;
}
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
return x_19;
}
}
else
{
uint8_t x_64; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_18 = l_Lean_Elab_Term_addLocalVarInfo(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_box(x_2);
x_21 = lean_box(x_6);
lean_inc_ref(x_10);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed), 13, 6);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_10);
lean_closure_set(x_22, 5, x_21);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_5);
x_23 = l_Lean_Elab_Term_elabLetDeclAux___lam__2(x_2, x_3, x_4, x_5, x_10, x_6, x_11, x_12, x_13, x_14, x_15, x_16, x_19);
if (lean_obj_tag(x_23) == 0)
{
if (x_8 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec_ref(x_5);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0;
x_27 = lean_array_push(x_26, x_10);
x_28 = 1;
x_29 = l_Lean_Meta_mkLetFVars(x_27, x_24, x_9, x_8, x_28, x_13, x_14, x_15, x_16, x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec_ref(x_23);
x_32 = l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0;
x_33 = lean_array_push(x_32, x_10);
x_34 = l_Lean_Expr_abstractM(x_30, x_33, x_13, x_14, x_15, x_16, x_31);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_expr_instantiate1(x_36, x_5);
lean_dec_ref(x_5);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_expr_instantiate1(x_38, x_5);
lean_dec_ref(x_5);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_dec_ref(x_5);
return x_34;
}
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
return x_23;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_5);
lean_inc_ref(x_10);
x_43 = l_Lean_Meta_mkEq(x_10, x_5, x_13, x_14, x_15, x_16, x_19);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_10);
x_46 = l_Lean_Meta_mkEqRefl(x_10, x_13, x_14, x_15, x_16, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = 1;
x_50 = lean_box(x_8);
x_51 = lean_box(x_6);
x_52 = lean_box(x_9);
x_53 = lean_box(x_49);
lean_inc(x_42);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed), 16, 8);
lean_closure_set(x_54, 0, x_42);
lean_closure_set(x_54, 1, x_22);
lean_closure_set(x_54, 2, x_50);
lean_closure_set(x_54, 3, x_51);
lean_closure_set(x_54, 4, x_10);
lean_closure_set(x_54, 5, x_52);
lean_closure_set(x_54, 6, x_53);
lean_closure_set(x_54, 7, x_5);
x_55 = l_Lean_Syntax_getId(x_42);
lean_dec(x_42);
x_56 = 0;
x_57 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_55, x_44, x_47, x_54, x_49, x_56, x_11, x_12, x_13, x_14, x_15, x_16, x_48);
return x_57;
}
else
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec_ref(x_22);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
return x_46;
}
}
else
{
lean_dec(x_42);
lean_dec_ref(x_22);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
return x_43;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected error when elaborating 'let'", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_5);
lean_inc_ref(x_5);
x_16 = l_Array_toSubarray___redArg(x_5, x_14, x_15);
x_17 = lean_array_size(x_1);
x_18 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__1(x_1, x_17, x_18, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_6);
x_22 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_23 = l_Lean_Elab_Term_elabTermEnsuringType(x_2, x_21, x_3, x_3, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = 0;
x_27 = 1;
x_28 = l_Lean_Meta_mkLambdaFVars(x_5, x_24, x_26, x_26, x_26, x_3, x_27, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_31 = l_Lean_Meta_isExprDefEq(x_4, x_29, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__1;
x_36 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_31, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_31, 0, x_39);
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
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
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
return x_19;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5;
x_2 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_21 = l_Lean_Elab_Term_elabBindersEx___redArg(x_1, x_2, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
x_31 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0;
x_32 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_31, x_18, x_24);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_68; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_box(x_4);
x_37 = lean_box(x_7);
x_38 = lean_box(x_9);
x_39 = lean_box(x_10);
lean_inc(x_29);
lean_inc(x_3);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__4___boxed), 17, 9);
lean_closure_set(x_40, 0, x_3);
lean_closure_set(x_40, 1, x_36);
lean_closure_set(x_40, 2, x_5);
lean_closure_set(x_40, 3, x_6);
lean_closure_set(x_40, 4, x_29);
lean_closure_set(x_40, 5, x_37);
lean_closure_set(x_40, 6, x_8);
lean_closure_set(x_40, 7, x_38);
lean_closure_set(x_40, 8, x_39);
x_41 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
x_42 = l_Lean_Elab_Term_kindOfBinderName(x_41);
x_68 = lean_unbox(x_34);
lean_dec(x_34);
if (x_68 == 0)
{
lean_free_object(x_32);
lean_free_object(x_23);
lean_free_object(x_22);
x_43 = x_14;
x_44 = x_15;
x_45 = x_16;
x_46 = x_17;
x_47 = x_18;
x_48 = x_19;
x_49 = x_35;
goto block_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
lean_inc(x_41);
x_70 = l_Lean_MessageData_ofName(x_41);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_70);
lean_ctor_set(x_32, 0, x_69);
x_71 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_71);
lean_ctor_set(x_23, 0, x_32);
lean_inc(x_26);
x_72 = l_Lean_MessageData_ofExpr(x_26);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_72);
lean_ctor_set(x_22, 0, x_23);
x_73 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_29);
x_75 = l_Lean_MessageData_ofExpr(x_29);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
x_78 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_31, x_77, x_16, x_17, x_18, x_19, x_35);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_43 = x_14;
x_44 = x_15;
x_45 = x_16;
x_46 = x_17;
x_47 = x_18;
x_48 = x_19;
x_49 = x_79;
goto block_67;
}
block_67:
{
lean_object* x_50; 
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_29);
lean_inc(x_26);
x_50 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_41, x_26, x_29, x_40, x_7, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49);
if (lean_obj_tag(x_50) == 0)
{
if (x_11 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_12);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_box(x_11);
lean_inc(x_30);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__5___boxed), 13, 4);
lean_closure_set(x_54, 0, x_30);
lean_closure_set(x_54, 1, x_12);
lean_closure_set(x_54, 2, x_53);
lean_closure_set(x_54, 3, x_29);
x_55 = lean_array_get_size(x_30);
lean_dec(x_30);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = 0;
x_58 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_26, x_56, x_54, x_57, x_57, x_43, x_44, x_45, x_46, x_47, x_48, x_52);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_51);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_51);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_12);
return x_50;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_113; 
x_80 = lean_ctor_get(x_32, 0);
x_81 = lean_ctor_get(x_32, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_32);
x_82 = lean_box(x_4);
x_83 = lean_box(x_7);
x_84 = lean_box(x_9);
x_85 = lean_box(x_10);
lean_inc(x_29);
lean_inc(x_3);
x_86 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__4___boxed), 17, 9);
lean_closure_set(x_86, 0, x_3);
lean_closure_set(x_86, 1, x_82);
lean_closure_set(x_86, 2, x_5);
lean_closure_set(x_86, 3, x_6);
lean_closure_set(x_86, 4, x_29);
lean_closure_set(x_86, 5, x_83);
lean_closure_set(x_86, 6, x_8);
lean_closure_set(x_86, 7, x_84);
lean_closure_set(x_86, 8, x_85);
x_87 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
x_88 = l_Lean_Elab_Term_kindOfBinderName(x_87);
x_113 = lean_unbox(x_80);
lean_dec(x_80);
if (x_113 == 0)
{
lean_free_object(x_23);
lean_free_object(x_22);
x_89 = x_14;
x_90 = x_15;
x_91 = x_16;
x_92 = x_17;
x_93 = x_18;
x_94 = x_19;
x_95 = x_81;
goto block_112;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
lean_inc(x_87);
x_115 = l_Lean_MessageData_ofName(x_87);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_117);
lean_ctor_set(x_23, 0, x_116);
lean_inc(x_26);
x_118 = l_Lean_MessageData_ofExpr(x_26);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_118);
lean_ctor_set(x_22, 0, x_23);
x_119 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_22);
lean_ctor_set(x_120, 1, x_119);
lean_inc(x_29);
x_121 = l_Lean_MessageData_ofExpr(x_29);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_114);
x_124 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_31, x_123, x_16, x_17, x_18, x_19, x_81);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
x_89 = x_14;
x_90 = x_15;
x_91 = x_16;
x_92 = x_17;
x_93 = x_18;
x_94 = x_19;
x_95 = x_125;
goto block_112;
}
block_112:
{
lean_object* x_96; 
lean_inc(x_94);
lean_inc_ref(x_93);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_29);
lean_inc(x_26);
x_96 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_87, x_26, x_29, x_86, x_7, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95);
if (lean_obj_tag(x_96) == 0)
{
if (x_11 == 0)
{
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_12);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = lean_box(x_11);
lean_inc(x_30);
x_100 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__5___boxed), 13, 4);
lean_closure_set(x_100, 0, x_30);
lean_closure_set(x_100, 1, x_12);
lean_closure_set(x_100, 2, x_99);
lean_closure_set(x_100, 3, x_29);
x_101 = lean_array_get_size(x_30);
lean_dec(x_30);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = 0;
x_104 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_26, x_102, x_100, x_103, x_103, x_89, x_90, x_91, x_92, x_93, x_94, x_98);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_97);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_12);
return x_96;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_164; 
x_126 = lean_ctor_get(x_23, 0);
x_127 = lean_ctor_get(x_23, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_23);
x_128 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0;
x_129 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_128, x_18, x_24);
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
x_133 = lean_box(x_4);
x_134 = lean_box(x_7);
x_135 = lean_box(x_9);
x_136 = lean_box(x_10);
lean_inc(x_126);
lean_inc(x_3);
x_137 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__4___boxed), 17, 9);
lean_closure_set(x_137, 0, x_3);
lean_closure_set(x_137, 1, x_133);
lean_closure_set(x_137, 2, x_5);
lean_closure_set(x_137, 3, x_6);
lean_closure_set(x_137, 4, x_126);
lean_closure_set(x_137, 5, x_134);
lean_closure_set(x_137, 6, x_8);
lean_closure_set(x_137, 7, x_135);
lean_closure_set(x_137, 8, x_136);
x_138 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
x_139 = l_Lean_Elab_Term_kindOfBinderName(x_138);
x_164 = lean_unbox(x_130);
lean_dec(x_130);
if (x_164 == 0)
{
lean_dec(x_132);
lean_free_object(x_22);
x_140 = x_14;
x_141 = x_15;
x_142 = x_16;
x_143 = x_17;
x_144 = x_18;
x_145 = x_19;
x_146 = x_131;
goto block_163;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_165 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
lean_inc(x_138);
x_166 = l_Lean_MessageData_ofName(x_138);
if (lean_is_scalar(x_132)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_132;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_26);
x_170 = l_Lean_MessageData_ofExpr(x_26);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_170);
lean_ctor_set(x_22, 0, x_169);
x_171 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_22);
lean_ctor_set(x_172, 1, x_171);
lean_inc(x_126);
x_173 = l_Lean_MessageData_ofExpr(x_126);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_165);
x_176 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_128, x_175, x_16, x_17, x_18, x_19, x_131);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec_ref(x_176);
x_140 = x_14;
x_141 = x_15;
x_142 = x_16;
x_143 = x_17;
x_144 = x_18;
x_145 = x_19;
x_146 = x_177;
goto block_163;
}
block_163:
{
lean_object* x_147; 
lean_inc(x_145);
lean_inc_ref(x_144);
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_126);
lean_inc(x_26);
x_147 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_138, x_26, x_126, x_137, x_7, x_139, x_140, x_141, x_142, x_143, x_144, x_145, x_146);
if (lean_obj_tag(x_147) == 0)
{
if (x_11 == 0)
{
lean_dec(x_145);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_26);
lean_dec(x_12);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_box(x_11);
lean_inc(x_127);
x_151 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__5___boxed), 13, 4);
lean_closure_set(x_151, 0, x_127);
lean_closure_set(x_151, 1, x_12);
lean_closure_set(x_151, 2, x_150);
lean_closure_set(x_151, 3, x_126);
x_152 = lean_array_get_size(x_127);
lean_dec(x_127);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = 0;
x_155 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_26, x_153, x_151, x_154, x_154, x_140, x_141, x_142, x_143, x_144, x_145, x_149);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_148);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_148);
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
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
}
else
{
lean_dec(x_145);
lean_dec_ref(x_144);
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_26);
lean_dec(x_12);
return x_147;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_218; 
x_178 = lean_ctor_get(x_22, 0);
lean_inc(x_178);
lean_dec(x_22);
x_179 = lean_ctor_get(x_23, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_23, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_181 = x_23;
} else {
 lean_dec_ref(x_23);
 x_181 = lean_box(0);
}
x_182 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0;
x_183 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_182, x_18, x_24);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_box(x_4);
x_188 = lean_box(x_7);
x_189 = lean_box(x_9);
x_190 = lean_box(x_10);
lean_inc(x_179);
lean_inc(x_3);
x_191 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__4___boxed), 17, 9);
lean_closure_set(x_191, 0, x_3);
lean_closure_set(x_191, 1, x_187);
lean_closure_set(x_191, 2, x_5);
lean_closure_set(x_191, 3, x_6);
lean_closure_set(x_191, 4, x_179);
lean_closure_set(x_191, 5, x_188);
lean_closure_set(x_191, 6, x_8);
lean_closure_set(x_191, 7, x_189);
lean_closure_set(x_191, 8, x_190);
x_192 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
x_193 = l_Lean_Elab_Term_kindOfBinderName(x_192);
x_218 = lean_unbox(x_184);
lean_dec(x_184);
if (x_218 == 0)
{
lean_dec(x_186);
lean_dec(x_181);
x_194 = x_14;
x_195 = x_15;
x_196 = x_16;
x_197 = x_17;
x_198 = x_18;
x_199 = x_19;
x_200 = x_185;
goto block_217;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_219 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
lean_inc(x_192);
x_220 = l_Lean_MessageData_ofName(x_192);
if (lean_is_scalar(x_186)) {
 x_221 = lean_alloc_ctor(7, 2, 0);
} else {
 x_221 = x_186;
 lean_ctor_set_tag(x_221, 7);
}
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2;
if (lean_is_scalar(x_181)) {
 x_223 = lean_alloc_ctor(7, 2, 0);
} else {
 x_223 = x_181;
 lean_ctor_set_tag(x_223, 7);
}
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
lean_inc(x_178);
x_224 = l_Lean_MessageData_ofExpr(x_178);
x_225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4;
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
lean_inc(x_179);
x_228 = l_Lean_MessageData_ofExpr(x_179);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_219);
x_231 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_182, x_230, x_16, x_17, x_18, x_19, x_185);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec_ref(x_231);
x_194 = x_14;
x_195 = x_15;
x_196 = x_16;
x_197 = x_17;
x_198 = x_18;
x_199 = x_19;
x_200 = x_232;
goto block_217;
}
block_217:
{
lean_object* x_201; 
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc(x_197);
lean_inc_ref(x_196);
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc(x_179);
lean_inc(x_178);
x_201 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_192, x_178, x_179, x_191, x_7, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200);
if (lean_obj_tag(x_201) == 0)
{
if (x_11 == 0)
{
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_12);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
x_204 = lean_box(x_11);
lean_inc(x_180);
x_205 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__5___boxed), 13, 4);
lean_closure_set(x_205, 0, x_180);
lean_closure_set(x_205, 1, x_12);
lean_closure_set(x_205, 2, x_204);
lean_closure_set(x_205, 3, x_179);
x_206 = lean_array_get_size(x_180);
lean_dec(x_180);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = 0;
x_209 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_178, x_207, x_205, x_208, x_208, x_194, x_195, x_196, x_197, x_198, x_199, x_203);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_202);
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_215 = x_209;
} else {
 lean_dec_ref(x_209);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
else
{
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_12);
return x_201;
}
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_233 = !lean_is_exclusive(x_21);
if (x_233 == 0)
{
return x_21;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_21, 0);
x_235 = lean_ctor_get(x_21, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_21);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`+postponeValue` and `+generalize` are incompatible", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_17 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 3);
x_19 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 4);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec_ref(x_7);
x_21 = lean_box(x_18);
x_22 = lean_box(x_15);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__0___boxed), 12, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_4);
lean_closure_set(x_23, 3, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed), 10, 1);
lean_closure_set(x_24, 0, x_5);
if (x_19 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Term_elabLetDeclAux___lam__6(x_2, x_23, x_1, x_19, x_24, x_6, x_15, x_20, x_17, x_16, x_18, x_4, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_26;
}
else
{
if (x_18 == 0)
{
lean_object* x_27; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_27 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Term_elabLetDeclAux___lam__6(x_2, x_23, x_1, x_19, x_24, x_6, x_15, x_20, x_17, x_16, x_18, x_4, x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = l_Lean_Elab_Term_elabLetDeclAux___closed__1;
x_36 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
x_15 = lean_unbox(x_6);
x_16 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
x_16 = lean_unbox(x_7);
x_17 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Term_elabLetDeclAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabLetDeclAux_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lam__0(x_1, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabLetDeclAux___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_6);
x_16 = l_Lean_Elab_Term_elabLetDeclAux___lam__2(x_14, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_3);
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_6);
x_20 = lean_unbox(x_7);
x_21 = l_Lean_Elab_Term_elabLetDeclAux___lam__3(x_1, x_2, x_17, x_18, x_5, x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__4___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_unbox(x_2);
x_19 = lean_unbox(x_6);
x_20 = lean_unbox(x_8);
x_21 = lean_unbox(x_9);
x_22 = l_Lean_Elab_Term_elabLetDeclAux___lam__4(x_1, x_18, x_3, x_4, x_5, x_19, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l_Lean_Elab_Term_elabLetDeclAux___lam__5(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclAux___lam__6___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_unbox(x_4);
x_22 = lean_unbox(x_7);
x_23 = lean_unbox(x_9);
x_24 = lean_unbox(x_10);
x_25 = lean_unbox(x_11);
x_26 = l_Lean_Elab_Term_elabLetDeclAux___lam__6(x_1, x_2, x_3, x_21, x_5, x_6, x_22, x_8, x_23, x_24, x_25, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_26;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkLetIdDeclView___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("this", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkLetIdDeclView___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArg(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_Elab_Term_mkLetIdDeclView___closed__1;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
x_2 = x_15;
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Elab_Term_mkLetIdDeclView___closed__3;
x_19 = l_Lean_HygieneInfo_mkIdent(x_15, x_18, x_17);
lean_dec(x_15);
x_2 = x_19;
goto block_12;
}
block_12:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Elab_Term_expandOptType(x_2, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(4u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
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
static lean_object* _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letIdDecl", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_6, x_2, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3;
x_18 = 0;
x_19 = l_Lean_mkAtomFrom(x_1, x_17, x_18);
x_20 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
x_21 = lean_array_push(x_20, x_12);
x_22 = lean_array_push(x_21, x_14);
x_23 = lean_array_push(x_22, x_16);
x_24 = lean_array_push(x_23, x_19);
x_25 = lean_array_push(x_24, x_9);
x_26 = lean_box(2);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__1;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
x_37 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3;
x_38 = 0;
x_39 = l_Lean_mkAtomFrom(x_1, x_37, x_38);
x_40 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__2;
x_41 = lean_array_push(x_40, x_32);
x_42 = lean_array_push(x_41, x_34);
x_43 = lean_array_push(x_42, x_36);
x_44 = lean_array_push(x_43, x_39);
x_45 = lean_array_push(x_44, x_28);
x_46 = lean_box(2);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_30);
lean_ctor_set(x_47, 2, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Elab_Term_expandLetEqnsDecl(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letPatDecl", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetDeclCore___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letEqnsDecl", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandFunBinders_loop___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`+zeta` with patterns is not allowed", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclCore___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`+usedOnly` with patterns is not allowed", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclCore___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`+deferValue` with patterns is not allowed", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDeclCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetDeclCore___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDeclCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = lean_unsigned_to_nat(1u);
x_304 = l_Lean_Syntax_getArg(x_1, x_303);
x_305 = l_Lean_Elab_Term_mkLetConfig___closed__1;
lean_inc(x_304);
x_306 = l_Lean_Syntax_isOfKind(x_304, x_305);
if (x_306 == 0)
{
lean_dec(x_304);
x_169 = x_3;
x_170 = x_303;
x_171 = x_4;
x_172 = x_5;
x_173 = x_6;
x_174 = x_7;
x_175 = x_8;
x_176 = x_9;
x_177 = x_10;
goto block_302;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = l_Lean_Elab_Term_mkLetConfig(x_304, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec_ref(x_307);
x_310 = lean_unsigned_to_nat(2u);
x_169 = x_308;
x_170 = x_310;
x_171 = x_4;
x_172 = x_5;
x_173 = x_6;
x_174 = x_7;
x_175 = x_8;
x_176 = x_9;
x_177 = x_309;
goto block_302;
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_box(x_11);
x_21 = lean_box(x_11);
lean_inc(x_12);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_22, 0, x_12);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_21);
x_23 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_12, x_22, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_23;
}
block_168:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_get(x_39, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_38, 5);
lean_inc(x_45);
x_46 = l_Lean_SourceInfo_fromRef(x_45, x_27);
lean_dec(x_45);
x_47 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_48 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_47);
lean_inc(x_46);
lean_ctor_set_tag(x_41, 2);
lean_ctor_set(x_41, 1, x_47);
lean_ctor_set(x_41, 0, x_46);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_50 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_46);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_53 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_52);
lean_inc_ref(x_51);
lean_inc(x_46);
x_54 = l_Lean_Syntax_node2(x_46, x_53, x_51, x_33);
lean_inc(x_46);
x_55 = l_Lean_Syntax_node1(x_46, x_49, x_54);
x_56 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_46);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_59 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_58);
x_60 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7;
x_61 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_60);
x_62 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_46);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_46);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_46);
x_64 = l_Lean_Syntax_node1(x_46, x_49, x_31);
lean_inc(x_46);
x_65 = l_Lean_Syntax_node1(x_46, x_49, x_64);
x_66 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_46);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_46);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_46);
x_68 = l_Lean_Syntax_node4(x_46, x_61, x_63, x_65, x_67, x_29);
lean_inc(x_46);
x_69 = l_Lean_Syntax_node1(x_46, x_49, x_68);
lean_inc(x_46);
x_70 = l_Lean_Syntax_node1(x_46, x_59, x_69);
lean_inc_ref(x_51);
x_71 = l_Lean_Syntax_node6(x_46, x_48, x_41, x_51, x_51, x_55, x_57, x_70);
x_11 = x_25;
x_12 = x_71;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
x_16 = x_37;
x_17 = x_38;
x_18 = x_39;
x_19 = x_43;
goto block_24;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_72 = lean_ctor_get(x_41, 1);
lean_inc(x_72);
lean_dec(x_41);
x_73 = lean_ctor_get(x_38, 5);
lean_inc(x_73);
x_74 = l_Lean_SourceInfo_fromRef(x_73, x_27);
lean_dec(x_73);
x_75 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_76 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_75);
lean_inc(x_74);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_79 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_74);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_82 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_81);
lean_inc_ref(x_80);
lean_inc(x_74);
x_83 = l_Lean_Syntax_node2(x_74, x_82, x_80, x_33);
lean_inc(x_74);
x_84 = l_Lean_Syntax_node1(x_74, x_78, x_83);
x_85 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_74);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_88 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_87);
x_89 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7;
x_90 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_89);
x_91 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_74);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_74);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_74);
x_93 = l_Lean_Syntax_node1(x_74, x_78, x_31);
lean_inc(x_74);
x_94 = l_Lean_Syntax_node1(x_74, x_78, x_93);
x_95 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_74);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_74);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_74);
x_97 = l_Lean_Syntax_node4(x_74, x_90, x_92, x_94, x_96, x_29);
lean_inc(x_74);
x_98 = l_Lean_Syntax_node1(x_74, x_78, x_97);
lean_inc(x_74);
x_99 = l_Lean_Syntax_node1(x_74, x_88, x_98);
lean_inc_ref(x_80);
x_100 = l_Lean_Syntax_node6(x_74, x_76, x_77, x_80, x_80, x_84, x_86, x_99);
x_11 = x_25;
x_12 = x_100;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
x_16 = x_37;
x_17 = x_38;
x_18 = x_39;
x_19 = x_72;
goto block_24;
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_28, 0);
lean_inc(x_101);
lean_dec(x_28);
x_102 = lean_st_ref_get(x_39, x_40);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_104 = lean_ctor_get(x_102, 1);
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = lean_ctor_get(x_38, 5);
lean_inc(x_106);
x_107 = l_Lean_SourceInfo_fromRef(x_106, x_27);
lean_dec(x_106);
x_108 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_109 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_108);
lean_inc(x_107);
lean_ctor_set_tag(x_102, 2);
lean_ctor_set(x_102, 1, x_108);
lean_ctor_set(x_102, 0, x_107);
x_110 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_111 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_107);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_111);
x_113 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_114 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_113);
x_115 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
lean_inc(x_107);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_107);
x_117 = l_Lean_Syntax_node2(x_107, x_110, x_101, x_116);
lean_inc(x_107);
x_118 = l_Lean_Syntax_node2(x_107, x_114, x_117, x_33);
lean_inc(x_107);
x_119 = l_Lean_Syntax_node1(x_107, x_110, x_118);
x_120 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_107);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_123 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_122);
x_124 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7;
x_125 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_124);
x_126 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_107);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_107);
lean_ctor_set(x_127, 1, x_126);
lean_inc(x_107);
x_128 = l_Lean_Syntax_node1(x_107, x_110, x_31);
lean_inc(x_107);
x_129 = l_Lean_Syntax_node1(x_107, x_110, x_128);
x_130 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_107);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_107);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_107);
x_132 = l_Lean_Syntax_node4(x_107, x_125, x_127, x_129, x_131, x_29);
lean_inc(x_107);
x_133 = l_Lean_Syntax_node1(x_107, x_110, x_132);
lean_inc(x_107);
x_134 = l_Lean_Syntax_node1(x_107, x_123, x_133);
lean_inc_ref(x_112);
x_135 = l_Lean_Syntax_node6(x_107, x_109, x_102, x_112, x_112, x_119, x_121, x_134);
x_11 = x_25;
x_12 = x_135;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
x_16 = x_37;
x_17 = x_38;
x_18 = x_39;
x_19 = x_104;
goto block_24;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_136 = lean_ctor_get(x_102, 1);
lean_inc(x_136);
lean_dec(x_102);
x_137 = lean_ctor_get(x_38, 5);
lean_inc(x_137);
x_138 = l_Lean_SourceInfo_fromRef(x_137, x_27);
lean_dec(x_137);
x_139 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_140 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_139);
lean_inc(x_138);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
x_143 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3;
lean_inc(x_138);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_143);
x_145 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_146 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_145);
x_147 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
lean_inc(x_138);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_138);
x_149 = l_Lean_Syntax_node2(x_138, x_142, x_101, x_148);
lean_inc(x_138);
x_150 = l_Lean_Syntax_node2(x_138, x_146, x_149, x_33);
lean_inc(x_138);
x_151 = l_Lean_Syntax_node1(x_138, x_142, x_150);
x_152 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4;
lean_inc(x_138);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_138);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5;
lean_inc_ref(x_30);
lean_inc_ref(x_26);
lean_inc_ref(x_32);
x_155 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_154);
x_156 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7;
x_157 = l_Lean_Name_mkStr4(x_32, x_26, x_30, x_156);
x_158 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9;
lean_inc(x_138);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_138);
lean_ctor_set(x_159, 1, x_158);
lean_inc(x_138);
x_160 = l_Lean_Syntax_node1(x_138, x_142, x_31);
lean_inc(x_138);
x_161 = l_Lean_Syntax_node1(x_138, x_142, x_160);
x_162 = l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10;
lean_inc(x_138);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_138);
lean_ctor_set(x_163, 1, x_162);
lean_inc(x_138);
x_164 = l_Lean_Syntax_node4(x_138, x_157, x_159, x_161, x_163, x_29);
lean_inc(x_138);
x_165 = l_Lean_Syntax_node1(x_138, x_142, x_164);
lean_inc(x_138);
x_166 = l_Lean_Syntax_node1(x_138, x_155, x_165);
lean_inc_ref(x_144);
x_167 = l_Lean_Syntax_node6(x_138, x_140, x_141, x_144, x_144, x_151, x_153, x_166);
x_11 = x_25;
x_12 = x_167;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
x_16 = x_37;
x_17 = x_38;
x_18 = x_39;
x_19 = x_136;
goto block_24;
}
}
}
block_302:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_178 = l_Lean_Syntax_getArg(x_1, x_170);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Lean_Syntax_getArg(x_178, x_179);
x_181 = lean_unsigned_to_nat(2u);
x_182 = lean_nat_add(x_170, x_181);
x_183 = l_Lean_Syntax_getArg(x_1, x_182);
lean_dec(x_182);
lean_inc(x_180);
x_184 = l_Lean_Syntax_getKind(x_180);
x_185 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_186 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_187 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_188 = l_Lean_Elab_Term_expandLetEqnsDecl___closed__1;
x_189 = lean_name_eq(x_184, x_188);
x_190 = 1;
if (x_189 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_Elab_Term_elabLetDeclCore___closed__1;
x_192 = lean_name_eq(x_184, x_191);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
lean_dec(x_183);
lean_dec_ref(x_169);
x_193 = l_Lean_Elab_Term_elabLetDeclCore___closed__3;
x_194 = lean_name_eq(x_184, x_193);
lean_dec(x_184);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_2);
lean_dec(x_1);
x_195 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_177);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_box(x_190);
x_197 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(x_197, 0, x_180);
lean_closure_set(x_197, 1, x_196);
lean_inc_ref(x_175);
lean_inc_ref(x_171);
x_198 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_197, x_171, x_172, x_173, x_174, x_175, x_176, x_177);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_201 = l_Lean_Syntax_setArg(x_178, x_179, x_199);
lean_inc(x_1);
x_202 = l_Lean_Syntax_setArg(x_1, x_170, x_201);
x_203 = lean_box(x_190);
x_204 = lean_box(x_190);
lean_inc(x_202);
x_205 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_205, 0, x_202);
lean_closure_set(x_205, 1, x_2);
lean_closure_set(x_205, 2, x_203);
lean_closure_set(x_205, 3, x_204);
x_206 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_202, x_205, x_171, x_172, x_173, x_174, x_175, x_176, x_200);
return x_206;
}
else
{
uint8_t x_207; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_2);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_198);
if (x_207 == 0)
{
return x_198;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_198, 0);
x_209 = lean_ctor_get(x_198, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_198);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_dec(x_184);
lean_dec(x_178);
x_211 = l_Lean_Syntax_getArg(x_180, x_179);
x_212 = l_Lean_Syntax_getArg(x_180, x_181);
x_213 = lean_unsigned_to_nat(4u);
x_214 = l_Lean_Syntax_getArg(x_180, x_213);
lean_dec(x_180);
lean_inc(x_211);
x_215 = l_Lean_Syntax_getKind(x_211);
x_216 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4;
x_217 = lean_name_eq(x_215, x_216);
lean_dec(x_215);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = lean_ctor_get_uint8(x_169, sizeof(void*)*1 + 3);
if (x_218 == 0)
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_169, sizeof(void*)*1 + 1);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = lean_ctor_get_uint8(x_169, sizeof(void*)*1 + 2);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_169, 0);
lean_inc(x_221);
lean_dec_ref(x_169);
x_222 = l_Lean_Syntax_isNone(x_212);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_st_ref_get(x_176, x_177);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_225 = lean_ctor_get(x_223, 1);
x_226 = lean_ctor_get(x_223, 0);
lean_dec(x_226);
x_227 = lean_ctor_get(x_175, 5);
lean_inc(x_227);
x_228 = l_Lean_Syntax_getArg(x_212, x_179);
lean_dec(x_212);
x_229 = lean_unsigned_to_nat(1u);
x_230 = l_Lean_Syntax_getArg(x_228, x_229);
lean_dec(x_228);
x_231 = l_Lean_SourceInfo_fromRef(x_227, x_222);
lean_dec(x_227);
x_232 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
x_233 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1;
lean_inc(x_231);
lean_ctor_set_tag(x_223, 2);
lean_ctor_set(x_223, 1, x_233);
lean_ctor_set(x_223, 0, x_231);
x_234 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
lean_inc(x_231);
x_235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_231);
x_237 = l_Lean_Syntax_node1(x_231, x_236, x_230);
x_238 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4;
lean_inc(x_231);
x_239 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_Syntax_node5(x_231, x_232, x_223, x_214, x_235, x_237, x_239);
x_25 = x_190;
x_26 = x_186;
x_27 = x_217;
x_28 = x_221;
x_29 = x_183;
x_30 = x_187;
x_31 = x_211;
x_32 = x_185;
x_33 = x_240;
x_34 = x_171;
x_35 = x_172;
x_36 = x_173;
x_37 = x_174;
x_38 = x_175;
x_39 = x_176;
x_40 = x_225;
goto block_168;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_241 = lean_ctor_get(x_223, 1);
lean_inc(x_241);
lean_dec(x_223);
x_242 = lean_ctor_get(x_175, 5);
lean_inc(x_242);
x_243 = l_Lean_Syntax_getArg(x_212, x_179);
lean_dec(x_212);
x_244 = lean_unsigned_to_nat(1u);
x_245 = l_Lean_Syntax_getArg(x_243, x_244);
lean_dec(x_243);
x_246 = l_Lean_SourceInfo_fromRef(x_242, x_222);
lean_dec(x_242);
x_247 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
x_248 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1;
lean_inc(x_246);
x_249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2;
lean_inc(x_246);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_246);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4;
lean_inc(x_246);
x_253 = l_Lean_Syntax_node1(x_246, x_252, x_245);
x_254 = l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4;
lean_inc(x_246);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_246);
lean_ctor_set(x_255, 1, x_254);
x_256 = l_Lean_Syntax_node5(x_246, x_247, x_249, x_214, x_251, x_253, x_255);
x_25 = x_190;
x_26 = x_186;
x_27 = x_217;
x_28 = x_221;
x_29 = x_183;
x_30 = x_187;
x_31 = x_211;
x_32 = x_185;
x_33 = x_256;
x_34 = x_171;
x_35 = x_172;
x_36 = x_173;
x_37 = x_174;
x_38 = x_175;
x_39 = x_176;
x_40 = x_241;
goto block_168;
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_212);
x_257 = lean_st_ref_get(x_176, x_177);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec_ref(x_257);
x_25 = x_190;
x_26 = x_186;
x_27 = x_217;
x_28 = x_221;
x_29 = x_183;
x_30 = x_187;
x_31 = x_211;
x_32 = x_185;
x_33 = x_214;
x_34 = x_171;
x_35 = x_172;
x_36 = x_173;
x_37 = x_174;
x_38 = x_175;
x_39 = x_176;
x_40 = x_258;
goto block_168;
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_183);
lean_dec_ref(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_259 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_260 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_259, x_171, x_172, x_173, x_174, x_175, x_176, x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
return x_260;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_260, 0);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_260);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_183);
lean_dec_ref(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_265 = l_Lean_Elab_Term_elabLetDeclCore___closed__8;
x_266 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_265, x_171, x_172, x_173, x_174, x_175, x_176, x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
return x_266;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_266, 0);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_266);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_183);
lean_dec_ref(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_271 = l_Lean_Elab_Term_elabLetDeclCore___closed__10;
x_272 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_271, x_171, x_172, x_173, x_174, x_175, x_176, x_177);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
return x_272;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_272);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
lean_object* x_277; 
lean_dec(x_1);
lean_inc(x_176);
lean_inc_ref(x_175);
x_277 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(x_211, x_190, x_175, x_176, x_177);
lean_dec(x_211);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec_ref(x_277);
x_280 = l_Lean_Elab_Term_expandOptType(x_278, x_212);
lean_dec(x_212);
x_281 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0;
x_282 = l_Lean_Elab_Term_elabLetDeclAux(x_278, x_281, x_280, x_214, x_183, x_2, x_169, x_171, x_172, x_173, x_174, x_175, x_176, x_279);
return x_282;
}
else
{
uint8_t x_283; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_183);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_277);
if (x_283 == 0)
{
return x_277;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_277, 0);
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_277);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
lean_dec(x_184);
lean_dec(x_178);
lean_dec(x_1);
x_287 = l_Lean_Elab_Term_mkLetIdDeclView(x_180);
lean_dec(x_180);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc_ref(x_289);
x_290 = lean_ctor_get(x_287, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_287, 3);
lean_inc(x_291);
lean_dec_ref(x_287);
x_292 = l_Lean_Syntax_isIdent(x_288);
if (x_292 == 0)
{
lean_object* x_293; 
lean_inc(x_176);
lean_inc_ref(x_175);
x_293 = l_Lean_Elab_Term_mkFreshIdent___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent_spec__0___redArg(x_288, x_190, x_175, x_176, x_177);
lean_dec(x_288);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = l_Lean_Elab_Term_elabLetDeclAux(x_294, x_289, x_290, x_291, x_183, x_2, x_169, x_171, x_172, x_173, x_174, x_175, x_176, x_295);
return x_296;
}
else
{
uint8_t x_297; 
lean_dec(x_291);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_183);
lean_dec(x_176);
lean_dec_ref(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_169);
lean_dec(x_2);
x_297 = !lean_is_exclusive(x_293);
if (x_297 == 0)
{
return x_293;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_293, 0);
x_299 = lean_ctor_get(x_293, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_293);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
lean_object* x_301; 
x_301 = l_Lean_Elab_Term_elabLetDeclAux(x_288, x_289, x_290, x_291, x_183, x_2, x_169, x_171, x_172, x_173, x_174, x_175, x_176, x_177);
return x_301;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 3, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 4, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabLetDecl___closed__0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabLetDecl", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__0;
x_4 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(27u);
x_2 = lean_unsigned_to_nat(773u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(129u);
x_2 = lean_unsigned_to_nat(774u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(129u);
x_2 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(27u);
x_4 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(773u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(42u);
x_2 = lean_unsigned_to_nat(773u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(42u);
x_2 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(31u);
x_4 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2;
x_3 = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveDecl___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabHaveDecl___closed__0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabHaveDecl", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__1;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__0;
x_4 = l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = 0;
x_10 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1_spec__1___redArg(x_1, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This linter can be disabled with `set_option ", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" false`", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1;
lean_inc(x_12);
x_15 = l_Lean_MessageData_ofName(x_12);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_14);
x_16 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_note(x_17);
x_19 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg(x_2, x_24, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1;
lean_inc(x_26);
x_28 = l_Lean_MessageData_ofName(x_26);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_note(x_31);
x_33 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
x_38 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg(x_2, x_38, x_6, x_7, x_8, x_9, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_8);
x_11 = l_Lean_Linter_getLinterOptions___at___Lean_Linter_checkDeprecated___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_checkDeprecatedCore_spec__0_spec__0(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Linter_getLinterValue(x_1, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; 
lean_free_object(x_11);
x_17 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = l_Lean_Linter_getLinterValue(x_1, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Linter_linter_deprecated;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`let_fun` has been deprecated in favor of `have`", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetFunDecl___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLetFunDecl___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 10);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_22 = lean_ctor_get(x_7, 11);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_24 = lean_ctor_get(x_7, 12);
lean_inc_ref(x_24);
x_25 = l_Lean_Elab_Term_elabLetFunDecl___closed__0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = l_Lean_Elab_Term_elabLetFunDecl___closed__3;
x_29 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_12);
lean_ctor_set(x_30, 3, x_13);
lean_ctor_set(x_30, 4, x_14);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_16);
lean_ctor_set(x_30, 7, x_17);
lean_ctor_set(x_30, 8, x_18);
lean_ctor_set(x_30, 9, x_19);
lean_ctor_set(x_30, 10, x_20);
lean_ctor_set(x_30, 11, x_22);
lean_ctor_set(x_30, 12, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_23);
x_31 = l_Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0(x_25, x_27, x_28, x_3, x_4, x_5, x_6, x_30, x_8, x_9);
lean_dec(x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Elab_Term_elabHaveDecl___closed__0;
x_34 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let_fun", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabLetFunDecl", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__1;
x_4 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetFunDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(776u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(130u);
x_2 = lean_unsigned_to_nat(777u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(130u);
x_2 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(31u);
x_4 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(776u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(776u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(35u);
x_4 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3;
x_3 = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabLetDelayedDecl___closed__0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let_delayed", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabLetDelayedDecl", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__1;
x_4 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetDelayedDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(779u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = lean_unsigned_to_nat(780u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(35u);
x_4 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(779u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = lean_unsigned_to_nat(779u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(39u);
x_4 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3;
x_3 = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabLetTmpDecl___closed__0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let_tmp", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabLetTmpDecl", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__1;
x_4 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetTmpDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(782u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = lean_unsigned_to_nat(783u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(31u);
x_4 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(782u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(782u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(35u);
x_4 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__5;
x_2 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3;
x_3 = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetIDecl___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetIDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabLetIDecl___closed__0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letI", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabLetIDecl", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__1;
x_4 = l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetIDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveIDecl___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveIDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabHaveIDecl___closed__0;
x_11 = l_Lean_Elab_Term_elabLetDeclCore(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("haveI", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__0;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabHaveIDecl", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__2;
x_2 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_3 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_4 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0;
x_3 = l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__1;
x_4 = l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHaveIDecl), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandWhereDecls___closed__4;
x_2 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_2 = l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2;
x_2 = l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_14753_;
x_2 = l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_Binders___hyg_14753_;
x_2 = l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0;
x_2 = l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8;
x_2 = l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Binders", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_Binders___hyg_14753_;
x_2 = l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_Binders___hyg_14753_;
x_2 = l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_Binders___hyg_14753_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(14753u);
x_2 = l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_14753_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_14753_;
x_3 = 0;
x_4 = l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_Binders___hyg_14753_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10;
x_11 = l_Lean_registerTraceClass(x_10, x_3, x_4, x_9);
return x_11;
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
}
lean_object* initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BindersUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Quotation_Precheck(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BindersUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderIdent___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandOptIdent___redArg___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_quoteAutoTactic_spec__0___closed__4);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__0);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__1);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__2 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__2();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__2);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__3 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__3();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__3);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__4 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__4();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__4);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__5);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__6 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__6();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__6);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__7 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__7();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__7);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__8);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__9 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__9();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__9);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__10);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__11);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__12 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__12();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__12);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__13 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__13();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__13);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__14);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__15);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__16 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__16();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__16);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__17 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__17();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__17);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__18 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__18();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__18);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__19);
l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__20 = _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__20();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Elab_Term_quoteAutoTactic_spec__1___closed__20);
l_Lean_Elab_Term_quoteAutoTactic___closed__0 = _init_l_Lean_Elab_Term_quoteAutoTactic___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_quoteAutoTactic___closed__0);
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
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__0);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__1 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__1);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__2);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__3 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__3);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__4 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__4);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__5 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__5);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__6 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__6);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__7);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__8);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__9);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__10);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__11 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__11);
l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__12 = _init_l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_declareTacticSyntax___redArg___lam__0___closed__12);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__9);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__10);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__11);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__12);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__13 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__13);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___redArg___closed__14);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__0 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__0);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__1);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_getBinderIds_spec__0_spec__0___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_toBinderViews___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__9 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__9);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__10 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__10);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__11 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_registerFailedToInferBinderTypeInfo___redArg___closed__11);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_ensureAtomicBinderName___closed__3);
l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_ = _init_l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_2354_);
l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_2354_ = _init_l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_2354_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_2354_);
l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_2354_ = _init_l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_2354_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_2354_);
l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_2354_ = _init_l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_2354_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_2354_);
l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_2354_ = _init_l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_2354_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_2354_);
if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_2354_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_checkBinderAnnotations = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_checkBinderAnnotations);
lean_dec_ref(res);
}l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkLocalInstanceParameters___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___redArg___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBindersAux___redArg___closed__0);
l_Lean_Elab_Term_elabBinder___redArg___closed__0 = _init_l_Lean_Elab_Term_elabBinder___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabBinder___redArg___closed__0);
l_Lean_Elab_Term_expandSimpleBinderWithType___closed__0 = _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandSimpleBinderWithType___closed__0);
l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1 = _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSimpleBinderWithType___closed__1);
l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2 = _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSimpleBinderWithType___closed__2);
l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3 = _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSimpleBinderWithType___closed__3);
l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4 = _init_l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSimpleBinderWithType___closed__4);
l_Lean_Elab_Term_expandForall___closed__0 = _init_l_Lean_Elab_Term_expandForall___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___closed__0);
l_Lean_Elab_Term_expandForall___closed__1 = _init_l_Lean_Elab_Term_expandForall___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___closed__1);
l_Lean_Elab_Term_expandForall___closed__2 = _init_l_Lean_Elab_Term_expandForall___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___closed__2);
l_Lean_Elab_Term_expandForall___closed__3 = _init_l_Lean_Elab_Term_expandForall___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___closed__3);
l_Lean_Elab_Term_expandForall___closed__4 = _init_l_Lean_Elab_Term_expandForall___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___closed__4);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__0);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__1 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__1);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1___closed__2);
if (builtin) {res = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__0 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__0);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__1 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__1);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__2 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__2);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__3 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__3);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__4 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__4);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__5 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__5);
l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__6 = _init_l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_expandForall___regBuiltin_Lean_Elab_Term_expandForall_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__0);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__1 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__1);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1___closed__2);
if (builtin) {res = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__0);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__1);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__2);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__3);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__4);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__5);
l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabForall___regBuiltin_Lean_Elab_Term_elabForall_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_precheckArrow___closed__0 = _init_l_Lean_Elab_Term_precheckArrow___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_precheckArrow___closed__0);
l_Lean_Elab_Term_precheckArrow___closed__1 = _init_l_Lean_Elab_Term_precheckArrow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_precheckArrow___closed__1);
l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0 = _init_l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__0);
l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__1 = _init_l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__1);
l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__2 = _init_l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1___closed__2);
if (builtin) {res = l_Lean_Elab_Term_precheckArrow___regBuiltin_Lean_Elab_Term_precheckArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabArrow___redArg___closed__0 = _init_l_Lean_Elab_Term_elabArrow___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___redArg___closed__0);
l_Lean_Elab_Term_elabArrow___redArg___closed__1 = _init_l_Lean_Elab_Term_elabArrow___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___redArg___closed__1);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__0 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__0);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1___closed__1);
if (builtin) {res = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__0);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__1);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__2);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__3);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__4);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__5);
l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabArrow___regBuiltin_Lean_Elab_Term_elabArrow_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__0 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__0);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__1 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__1);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__2 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__2);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1___closed__3);
if (builtin) {res = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3___closed__0 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3___closed__0);
if (builtin) {res = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_docString__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__0 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__0);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__1 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__1);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__2 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__2);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__3 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__3);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__4 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__4);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__5 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__5);
l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__6 = _init_l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabDepArrow___regBuiltin_Lean_Elab_Term_elabDepArrow_declRange__5(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_getFunBinderIds_x3f___closed__0);
l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0 = _init_l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__0);
l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1 = _init_l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at___Lean_Elab_Term_mkFreshIdent___at___Lean_Elab_Term_expandFunBinders_loop_spec__0_spec__0___closed__1);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__0);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__1);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__2);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__3);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__4);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__5);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__6);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__7);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__8);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__9);
l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10 = _init_l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___lam__0___closed__10);
l_Lean_Elab_Term_expandFunBinders_loop___closed__0 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__0);
l_Lean_Elab_Term_expandFunBinders_loop___closed__1 = _init_l_Lean_Elab_Term_expandFunBinders_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandFunBinders_loop___closed__1);
l_Lean_Elab_Term_elabFunBinders___redArg___closed__0 = _init_l_Lean_Elab_Term_elabFunBinders___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabFunBinders___redArg___closed__0);
l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandWhereDecls_spec__0___closed__0);
l_Lean_Elab_Term_expandWhereDecls___closed__0 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__0);
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
l_Lean_Elab_Term_expandWhereDecls___closed__11 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__11);
l_Lean_Elab_Term_expandWhereDecls___closed__12 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__12);
l_Lean_Elab_Term_expandWhereDecls___closed__13 = _init_l_Lean_Elab_Term_expandWhereDecls___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_expandWhereDecls___closed__13);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandMatchAltsIntoMatchAux___closed__0);
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
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts_spec__0_spec__0___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__1___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___lam__2___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__0 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__0);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__1);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__2 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__2);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__3);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__4 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__4);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__5);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__6 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__6);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__7);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__8 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__8);
l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9 = _init_l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Binders_0__Lean_Elab_Term_checkMatchAltPatternCounts___closed__9);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__0 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__0);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1___closed__1);
if (builtin) {res = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__0 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__0);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__1 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__1);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__2 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__2);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__3 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__3);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__4 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__4);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__5 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__5);
l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__6 = _init_l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_expandFun___regBuiltin_Lean_Elab_Term_expandFun_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__0 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__0);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1___closed__1);
if (builtin) {res = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__0 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__0);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__1 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__1);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__2 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__2);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__3 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__3);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__4 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__4);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__5 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__5);
l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__6 = _init_l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_expandExplicitFun___regBuiltin_Lean_Elab_Term_expandExplicitFun_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_precheckFun___closed__0 = _init_l_Lean_Elab_Term_precheckFun___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_precheckFun___closed__0);
l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__0 = _init_l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__0);
l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__1 = _init_l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1___closed__1);
if (builtin) {res = l_Lean_Elab_Term_precheckFun___regBuiltin_Lean_Elab_Term_precheckFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__0 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__0);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1___closed__1);
if (builtin) {res = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__0);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__1);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__2);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__3);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__4);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__5);
l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabFun___regBuiltin_Lean_Elab_Term_elabFun_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_LetConfig_setFrom___closed__0 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__0);
l_Lean_Elab_Term_LetConfig_setFrom___closed__1 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__1);
l_Lean_Elab_Term_LetConfig_setFrom___closed__2 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__2);
l_Lean_Elab_Term_LetConfig_setFrom___closed__3 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__3);
l_Lean_Elab_Term_LetConfig_setFrom___closed__4 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__4);
l_Lean_Elab_Term_LetConfig_setFrom___closed__5 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__5);
l_Lean_Elab_Term_LetConfig_setFrom___closed__6 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__6);
l_Lean_Elab_Term_LetConfig_setFrom___closed__7 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__7);
l_Lean_Elab_Term_LetConfig_setFrom___closed__8 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__8);
l_Lean_Elab_Term_LetConfig_setFrom___closed__9 = _init_l_Lean_Elab_Term_LetConfig_setFrom___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_LetConfig_setFrom___closed__9);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__4);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__5);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__6);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__7);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__8);
l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkLetConfig_spec__0___redArg___closed__9);
l_Lean_Elab_Term_mkLetConfig___closed__0 = _init_l_Lean_Elab_Term_mkLetConfig___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_mkLetConfig___closed__0);
l_Lean_Elab_Term_mkLetConfig___closed__1 = _init_l_Lean_Elab_Term_mkLetConfig___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkLetConfig___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__3);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__4 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__4);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__5);
l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__0___closed__6);
l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__2___closed__3);
l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__3___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__4___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__5___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__1);
l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__2);
l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__3);
l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4 = _init_l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___lam__6___closed__4);
l_Lean_Elab_Term_elabLetDeclAux___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__0);
l_Lean_Elab_Term_elabLetDeclAux___closed__1 = _init_l_Lean_Elab_Term_elabLetDeclAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclAux___closed__1);
l_Lean_Elab_Term_mkLetIdDeclView___closed__0 = _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_mkLetIdDeclView___closed__0);
l_Lean_Elab_Term_mkLetIdDeclView___closed__1 = _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkLetIdDeclView___closed__1);
l_Lean_Elab_Term_mkLetIdDeclView___closed__2 = _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkLetIdDeclView___closed__2);
l_Lean_Elab_Term_mkLetIdDeclView___closed__3 = _init_l_Lean_Elab_Term_mkLetIdDeclView___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkLetIdDeclView___closed__3);
l_Lean_Elab_Term_expandLetEqnsDecl___closed__0 = _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_expandLetEqnsDecl___closed__0);
l_Lean_Elab_Term_expandLetEqnsDecl___closed__1 = _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandLetEqnsDecl___closed__1);
l_Lean_Elab_Term_expandLetEqnsDecl___closed__2 = _init_l_Lean_Elab_Term_expandLetEqnsDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandLetEqnsDecl___closed__2);
l_Lean_Elab_Term_elabLetDeclCore___closed__0 = _init_l_Lean_Elab_Term_elabLetDeclCore___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDeclCore___closed__0);
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
l_Lean_Elab_Term_elabLetDecl___closed__0 = _init_l_Lean_Elab_Term_elabLetDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___closed__0);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__0);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__1);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1___closed__2);
if (builtin) {res = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__0);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__1);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__2);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__3);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__4);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__5);
l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabLetDecl___regBuiltin_Lean_Elab_Term_elabLetDecl_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabHaveDecl___closed__0 = _init_l_Lean_Elab_Term_elabHaveDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveDecl___closed__0);
l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__0);
l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__1);
l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1___closed__2);
if (builtin) {res = l_Lean_Elab_Term_elabHaveDecl___regBuiltin_Lean_Elab_Term_elabHaveDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__0 = _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__0);
l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1 = _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__1);
l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__2 = _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__2);
l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3 = _init_l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Term_elabLetFunDecl_spec__0_spec__0___closed__3);
l_Lean_Elab_Term_elabLetFunDecl___closed__0 = _init_l_Lean_Elab_Term_elabLetFunDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___closed__0);
l_Lean_Elab_Term_elabLetFunDecl___closed__1 = _init_l_Lean_Elab_Term_elabLetFunDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___closed__1);
l_Lean_Elab_Term_elabLetFunDecl___closed__2 = _init_l_Lean_Elab_Term_elabLetFunDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___closed__2);
l_Lean_Elab_Term_elabLetFunDecl___closed__3 = _init_l_Lean_Elab_Term_elabLetFunDecl___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___closed__3);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__0);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__1);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__2);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1___closed__3);
if (builtin) {res = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__0);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__1);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__2);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__3);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__4);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__5);
l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabLetFunDecl___regBuiltin_Lean_Elab_Term_elabLetFunDecl_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetDelayedDecl___closed__0 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___closed__0);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__0);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__1);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__2);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1___closed__3);
if (builtin) {res = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__0);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__1);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__2);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__3);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__4);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__5);
l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabLetDelayedDecl___regBuiltin_Lean_Elab_Term_elabLetDelayedDecl_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetTmpDecl___closed__0 = _init_l_Lean_Elab_Term_elabLetTmpDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___closed__0);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__0);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__1);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__2);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1___closed__3);
if (builtin) {res = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__0 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__0);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__1 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__1);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__2 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__2);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__3 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__3);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__4 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__4);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__5 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__5);
l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__6 = _init_l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Term_elabLetTmpDecl___regBuiltin_Lean_Elab_Term_elabLetTmpDecl_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabLetIDecl___closed__0 = _init_l_Lean_Elab_Term_elabLetIDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetIDecl___closed__0);
l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__0);
l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__1);
l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__2);
l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__3 = _init_l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1___closed__3);
if (builtin) {res = l_Lean_Elab_Term_elabLetIDecl___regBuiltin_Lean_Elab_Term_elabLetIDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_elabHaveIDecl___closed__0 = _init_l_Lean_Elab_Term_elabHaveIDecl___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveIDecl___closed__0);
l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__0 = _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__0);
l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__1 = _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__1);
l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__2 = _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__2);
l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__3 = _init_l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1___closed__3);
if (builtin) {res = l_Lean_Elab_Term_elabHaveIDecl___regBuiltin_Lean_Elab_Term_elabHaveIDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_Binders___hyg_14753_);
l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_Binders___hyg_14753_ = _init_l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_Binders___hyg_14753_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_Binders___hyg_14753_);
if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Binders___hyg_14753_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
